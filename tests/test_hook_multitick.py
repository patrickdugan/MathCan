"""CHTR-10 independent mutation tests. Foundry executes real code in pinned CI."""
import copy
import unittest

from research.chitraverse import hook_multitick as f
from research.chitraverse.foundry_opcode import Q96, tick_price_x96
from research.chitraverse.v4_delta_refinement import keccak256


def fabricated_observation():
    q=f.quote_multitick()
    manager_blob="0x6001600055"
    hook_blob="0x6002600055"
    mgr_art={"deployedBytecode":{"object":manager_blob,"immutableReferences":{}}}
    hook_art={"deployedBytecode":{"object":hook_blob,"immutableReferences":{}}}
    obs={
        "schema":f.SCHEMA,
        "core_commit":f.CORE_COMMIT,
        "manager":"0x"+"1"*40,
        "router":"0x"+"2"*40,
        "hook":"0x"+"3"*40,
        "currency0":"0x"+"4"*40,
        "currency1":"0x"+"5"*40,
        "pool_id":"0x"+"6"*64,
        "manager_runtime_hash":"0x"+keccak256(bytes.fromhex(manager_blob[2:])).hex(),
        "hook_runtime_hash":"0x"+keccak256(bytes.fromhex(hook_blob[2:])).hex(),
        "amount_specified":-f.GROSS,
        "before_specified":f.SPECIFIED,
        "before_unspecified":f.BEFORE_UNSPECIFIED,
        "after_unspecified":f.AFTER_UNSPECIFIED,
        "pool_delta0":-f.POOL_INPUT,
        "pool_delta1":q["total_output"],
        "caller_delta0":-f.GROSS,
        "caller_delta1":q["total_output"]-f.HOOK_UNSPECIFIED,
        "hook_delta0":f.SPECIFIED,
        "hook_delta1":f.HOOK_UNSPECIFIED,
        "event_delta0":-f.POOL_INPUT,
        "event_delta1":q["total_output"],
        "fee_pips":f.FEE,
        "sqrt_price_before_x96":Q96,
        "sqrt_price_after_x96":q["sqrt_price_after_x96"],
        "tick_before":0,
        "tick_after":q["terminal_tick"],
        "liquidity_before":10**18,
        "liquidity_after":4*10**18,
        "nonzero_at_swap":4,
        "nonzero_after_settlement":0,
        "trader0_before":2*f.GROSS,
        "trader0_after":f.GROSS,
        "trader1_before":0,
        "trader1_after":q["total_output"]-f.HOOK_UNSPECIFIED,
        "hook0_before":0,
        "hook0_after":f.SPECIFIED,
        "hook1_before":0,
        "hook1_after":f.HOOK_UNSPECIFIED,
        "vault0_before":2*f.GROSS,
        "vault0_after":2*f.GROSS + f.POOL_INPUT,
        "vault1_before":2*f.GROSS,
        "vault1_after":2*f.GROSS - q["total_output"],
        "debug_step_count":2000,
    }
    pairs=f.expected_manager_tstores(obs,q)
    obs["manager_tstore_pairs"]=[x for pair in pairs for x in pair]
    obs["manager_tstore_count"]=len(pairs)
    return obs,mgr_art,hook_art


class HookMultitickTests(unittest.TestCase):
    def test_exact_tick_values(self):
        q=f.quote_multitick()
        self.assertEqual(q["crossed_ticks"],[-120,-240,-360])
        self.assertEqual(q["total_output"],47583989168610240)
        self.assertEqual(q["sqrt_price_after_x96"],77577612008717379644593744931)
        self.assertEqual(q["terminal_tick"],-422)
        self.assertEqual(q["active_liquidity_after"],4*10**18)
        self.assertGreater(q["sqrt_price_after_x96"],tick_price_x96(-480))
        self.assertLess(q["sqrt_price_after_x96"],tick_price_x96(-360))

    def test_exact_rounding_and_conservation(self):
        q=f.quote_multitick()
        self.assertEqual(sum(s["gross_spent"] for s in q["steps"]),f.POOL_INPUT)
        self.assertEqual(sum(s["output"] for s in q["steps"]),q["total_output"])
        for s in q["steps"]:
            self.assertEqual(s["gross_spent"],s["effective_input"]+s["fee_amount"])

    def test_crossing_precondition_fails_closed(self):
        with self.assertRaisesRegex(f.ProofError,"exactly three"):
            f.quote_multitick(10**15)
        with self.assertRaisesRegex(f.ProofError,"exactly three"):
            f.quote_multitick(10**17)

    def test_happy_trace(self):
        obs,mgr,hook=fabricated_observation()
        got=f.verify_trace(obs,mgr,hook)
        self.assertEqual(got["manager_tstores"],21)
        self.assertEqual(got["caller_output"],str(47578989168610240))
        self.assertTrue(got["both_runtime_artifacts_matched"])

    def test_hook_and_caller_delta_are_separate(self):
        obs,mgr,hook=fabricated_observation()
        self.assertEqual(obs["pool_delta0"],obs["caller_delta0"]+obs["hook_delta0"])
        self.assertEqual(obs["pool_delta1"],obs["caller_delta1"]+obs["hook_delta1"])

    def test_written_delta_slot_order(self):
        obs,_,_=fabricated_observation()
        pairs=f.expected_manager_tstores(obs,f.quote_multitick())
        self.assertEqual(pairs[1][0],f.delta_slot(obs["hook"],obs["currency0"]))
        self.assertEqual(pairs[5][0],f.delta_slot(obs["router"],obs["currency0"]))
        self.assertEqual(pairs[-1],(f.LOCK_SLOT,f.word(0)))

    def check_bad(self,field,new,contains):
        obs,mgr,hook=fabricated_observation()
        obs[field]=new
        with self.assertRaisesRegex(f.ProofError,contains):f.verify_trace(obs,mgr,hook)

    def test_wrong_pool_output(self): self.check_bad("pool_delta1",1,"pool_delta1")
    def test_wrong_tick(self): self.check_bad("tick_after",-121,"tick_after")
    def test_wrong_price(self): self.check_bad("sqrt_price_after_x96",Q96,"sqrt_price_after_x96")
    def test_wrong_liquidity(self): self.check_bad("liquidity_after",3*10**18,"liquidity_after")
    def test_wrong_hook_specified(self): self.check_bad("hook_delta0",f.SPECIFIED-1,"hook_delta0")
    def test_wrong_hook_unspecified(self): self.check_bad("hook_delta1",f.HOOK_UNSPECIFIED+1,"hook_delta1")
    def test_wrong_before_delta(self): self.check_bad("before_unspecified",0,"before_unspecified")
    def test_wrong_after_delta(self): self.check_bad("after_unspecified",0,"after_unspecified")
    def test_wrong_source_pin(self): self.check_bad("core_commit","0"*40,"source commit")
    def test_wrong_fee(self): self.check_bad("fee_pips",0,"fee_pips")
    def test_zero_crossing_forged(self): self.check_bad("nonzero_at_swap",2,"nonzero_at_swap")

    def test_missing_write_rejected(self):
        obs,mgr,hook=fabricated_observation()
        del obs["manager_tstore_pairs"][8:10]
        obs["manager_tstore_count"]-=1
        with self.assertRaisesRegex(f.ProofError,"ordered manager TSTORE"):
            f.verify_trace(obs,mgr,hook)

    def test_reordered_write_rejected(self):
        obs,mgr,hook=fabricated_observation()
        obs["manager_tstore_pairs"][2:4],obs["manager_tstore_pairs"][4:6]=(
            obs["manager_tstore_pairs"][4:6],obs["manager_tstore_pairs"][2:4])
        with self.assertRaisesRegex(f.ProofError,"ordered manager TSTORE"):
            f.verify_trace(obs,mgr,hook)

    def test_counter_value_forged(self):
        obs,mgr,hook=fabricated_observation()
        obs["manager_tstore_pairs"][5]=f.word(0)
        with self.assertRaisesRegex(f.ProofError,"ordered manager TSTORE"):
            f.verify_trace(obs,mgr,hook)

    def test_trader_value_forged(self):
        obs,mgr,hook=fabricated_observation()
        obs["trader1_after"]+=1
        with self.assertRaisesRegex(f.ProofError,"trader1"):
            f.verify_trace(obs,mgr,hook)

    def test_hook_value_forged(self):
        obs,mgr,hook=fabricated_observation()
        obs["hook1_after"]+=1
        with self.assertRaisesRegex(f.ProofError,"hook1"):
            f.verify_trace(obs,mgr,hook)

    def test_vault_value_forged(self):
        obs,mgr,hook=fabricated_observation()
        obs["vault0_after"]+=1
        with self.assertRaisesRegex(f.ProofError,"vault0"):
            f.verify_trace(obs,mgr,hook)

    def test_manager_bytecode_mismatch(self):
        obs,mgr,hook=fabricated_observation()
        mgr["deployedBytecode"]["object"]="0x6000600055"
        with self.assertRaisesRegex(f.ProofError,"PoolManager runtime hash"):
            f.verify_trace(obs,mgr,hook)

    def test_hook_bytecode_mismatch(self):
        obs,mgr,hook=fabricated_observation()
        hook["deployedBytecode"]["object"]="0x6000600055"
        with self.assertRaisesRegex(f.ProofError,"hook runtime hash"):
            f.verify_trace(obs,mgr,hook)

    def test_requires_both_artifacts(self):
        obs,mgr,hook=fabricated_observation()
        with self.assertRaisesRegex(f.ProofError,"hook artifact required"):
            f.verify_trace(obs,mgr)
        with self.assertRaisesRegex(f.ProofError,"PoolManager artifact required"):
            f.verify_trace(obs,None,hook)

    def test_manager_immutable_instantiation(self):
        obs,mgr,hook=fabricated_observation()
        blob=b"\x60"*4+b"\x00"*32+b"\x55"
        mgr["deployedBytecode"]={"object":"0x"+blob.hex(),
                                  "immutableReferences":{"349":[{"start":4,"length":32}]}}
        patched=blob[:4]+int(obs["manager"],16).to_bytes(32,"big")+blob[36:]
        obs["manager_runtime_hash"]="0x"+keccak256(patched).hex()
        self.assertTrue(f.verify_trace(obs,mgr,hook)["verified"])

    def test_invalid_event_runtime_sha(self):
        obs,mgr,hook=fabricated_observation()
        obs["hook_runtime_hash"]="0x"+"f"*64
        with self.assertRaisesRegex(f.ProofError,"hook runtime hash"):
            f.verify_trace(obs,mgr,hook)


if __name__=="__main__":unittest.main()
