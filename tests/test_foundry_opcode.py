"""CHTR-09 synthetic mutation tests; actual EVM measurement runs in pinned Foundry CI."""
import copy
import unittest
from research.chitraverse import foundry_opcode as f
from research.chitraverse.v4_delta_refinement import keccak256


def fake():
    q=f.quote_two_ticks()
    runtime='0x6001600055'
    artifact={'deployedBytecode':{'object':runtime, 'immutableReferences':{}}}
    obs={
        'schema':f.SCHEMA,
        'core_commit':f.CORE_COMMIT,
        'manager':'0x'+'1'*40,
        'probe_router':'0x'+'2'*40,
        'hook':'0x'+'3'*40,
        'currency0':'0x'+'4'*40,
        'currency1':'0x'+'5'*40,
        'pool_id':'0x'+'6'*64,
        'manager_runtime_hash':'0x'+keccak256(bytes.fromhex(runtime[2:])).hex(),
        'sqrt_price_before_x96':f.Q96,
        'boundary_price_x96':q['boundary_price_x96'],
        'sqrt_price_after_x96':q['sqrt_price_after_x96'],
        'liquidity_before':f.L_UPPER,
        'liquidity_after':f.L_LOWER,
        'tick_before':0,
        'tick_after':-161,
        'swap_amount_specified':-f.GROSS_INPUT,
        'caller_delta0':-f.GROSS_INPUT,
        'caller_delta1':q['total_output'],
        'event_delta0':-f.GROSS_INPUT,
        'event_delta1':q['total_output'],
        'event_fee_pips':f.FEE,
        'nonzero_at_swap':2,
        'nonzero_after_settlement':0,
        'hooks_observed':True,
        'swap_log_observed':True,
        'trader0_before':2*f.GROSS_INPUT,
        'trader0_after':f.GROSS_INPUT,
        'trader1_before':0,
        'trader1_after':q['total_output'],
        'vault0_before':f.GROSS_INPUT,
        'vault0_after':2*f.GROSS_INPUT,
        'vault1_before':2*f.GROSS_INPUT,
        'vault1_after':2*f.GROSS_INPUT-q['total_output'],
    }
    pairs=f.expected_manager_tstores(obs,q)
    obs['manager_tstore_pairs']=[x for pair in pairs for x in pair]
    obs['manager_tstore_count']=len(pairs)
    obs['debug_step_count']=1000
    return obs,artifact

class TestTickCertificate(unittest.TestCase):
    def test_pinned_tick_math(self):
        self.assertEqual(f.tick_price_x96(0), f.Q96)
        self.assertEqual(f.tick_price_x96(-120), 78754240422856966435523493930)
        self.assertGreater(f.tick_price_x96(-120), f.tick_price_x96(-240))
        self.assertEqual(f.tick_price_x96(120), 79704936542881920863903188246)

    def test_exact_two_step(self):
        q=f.quote_two_ticks()
        self.assertEqual(q['total_output'], 9879206229426645)
        self.assertEqual(q['sqrt_price_after_x96'], 78599845790232178562796990934)
        self.assertEqual(q['input_step1']+q['net_input_step2']+q['fee_step2'],f.GROSS_INPUT)
        self.assertLess(q['sqrt_price_after_x96'],q['boundary_price_x96'])

    def test_small_amount_no_cross(self):
        with self.assertRaises(f.ProofError):f.quote_two_ticks(10**10)

    def test_overshoot_second_tick(self):
        with self.assertRaises(f.ProofError):f.quote_two_ticks(10**17)

    def test_happy_complete(self):
        obs,art=fake()
        self.assertEqual(f.verify_trace(obs,art)['manager_tstores'],13)

    def test_bytecode_mismatch(self):
        obs,art=fake();art['deployedBytecode']['object']='0x6002600055'
        with self.assertRaisesRegex(f.ProofError,'compiled PoolManager'):f.verify_trace(obs,art)

    def test_real_no_delegatecall_immutable_resolved(self):
        obs,art=fake()
        # Sole immutable source is NoDelegateCall.original = address(this).
        blob=b'\x60'*4 + b'\x00'*32 + b'\x55'
        art['deployedBytecode']={
            'object':'0x'+blob.hex(),
            'immutableReferences':{'349':[{'start':4,'length':32}]},
        }
        patched=blob[:4]+int(obs['manager'],16).to_bytes(32,'big')+blob[36:]
        obs['manager_runtime_hash']='0x'+keccak256(patched).hex()
        self.assertTrue(f.verify_trace(obs,art)['artifact_runtime_matched'])

    def test_unsupported_immutable_shape_rejected(self):
        obs,art=fake()
        art['deployedBytecode']['immutableReferences']={'123':[{'start':3,'length':20}]}
        with self.assertRaisesRegex(f.ProofError,'unsafe immutable'):f.verify_trace(obs,art)

    def test_multiple_immutables_rejected(self):
        obs,art=fake()
        art['deployedBytecode']['immutableReferences']={
          '1':[{'start':0,'length':32}], '2':[{'start':1,'length':32}]}
        with self.assertRaisesRegex(f.ProofError,'unsupported immutable'):f.verify_trace(obs,art)

    def test_swapped_tstores_rejected(self):
        obs,art=fake();obs['manager_tstore_pairs'][2:4],obs['manager_tstore_pairs'][4:6]=obs['manager_tstore_pairs'][4:6],obs['manager_tstore_pairs'][2:4]
        with self.assertRaisesRegex(f.ProofError,'ordered TSTORE'):f.verify_trace(obs,art)

    def test_tstore_omission_rejected(self):
        obs,art=fake();del obs['manager_tstore_pairs'][4:6];obs['manager_tstore_count']-=1
        with self.assertRaisesRegex(f.ProofError,'ordered TSTORE'):f.verify_trace(obs,art)

    def test_forged_credit_rejected(self):
        obs,art=fake();obs['manager_tstore_pairs'][7]='0x'+'00'*31+'07'
        with self.assertRaisesRegex(f.ProofError,'ordered TSTORE'):f.verify_trace(obs,art)

    def test_untied_artifact_pin_rejected(self):
        obs,art=fake();obs['core_commit']='0'*40
        with self.assertRaisesRegex(f.ProofError,'source pin'):f.verify_trace(obs,art)

    def test_forged_tick_rejected(self):
        obs,art=fake();obs['tick_after']=-50
        with self.assertRaisesRegex(f.ProofError,'crossed'):f.verify_trace(obs,art)

    def test_forged_fee_rejected(self):
        obs,art=fake();obs['event_fee_pips']=0
        with self.assertRaisesRegex(f.ProofError,'event_fee'):f.verify_trace(obs,art)

    def test_forged_liquidity_rejected(self):
        obs,art=fake();obs['liquidity_after']=f.L_UPPER
        with self.assertRaisesRegex(f.ProofError,'liquidity_after'):f.verify_trace(obs,art)

    def test_wrong_vault_movement_rejected(self):
        obs,art=fake();obs['vault1_after']+=1
        with self.assertRaisesRegex(f.ProofError,'balance conservation'):f.verify_trace(obs,art)

    def test_missing_hook_rejected(self):
        obs,art=fake();obs['hooks_observed']=False
        with self.assertRaisesRegex(f.ProofError,'hook calls'):f.verify_trace(obs,art)

    def test_delta_slot_ethereum_keccak(self):
        obs,art=fake();q=f.quote_two_ticks()
        seq=f.expected_manager_tstores(obs,q)
        self.assertEqual(seq[1][1],f.word(-f.GROSS_INPUT))
        self.assertEqual(seq[0][0],f.LOCK_SLOT)
        self.assertEqual(seq[-1][1],f.word(0))

if __name__=='__main__':unittest.main()
