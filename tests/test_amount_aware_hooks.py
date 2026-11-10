"""CHTR-04 exact checks, including exhaustive small finite rate/amount grids."""
import unittest
from fractions import Fraction as F

from research.chitraverse.amount_aware_hooks import (
    Wallet, Pool, HookRule, HookProgram, Market, Trade,
    execute, execute_route, baseline_gap, constant_program, optimal_route,
    wallet_value, _totals, general_budget, lower_sqrt_rational,
)


def program_two_phase(n, phase0=(F(1),F(1)), phase1=(F(1,2),F(1,2))):
    return HookProgram(tuple(tuple((HookRule(fee[0], 1-i), HookRule(fee[1], 1-i))
                                  for _ in range(n))
                             for i,fee in enumerate((phase0,phase1))))


class StatefulAmountAwareTests(unittest.TestCase):
    def test_cross_pool_mispricing_real_proceeds(self):
        initial = Market((Pool(100,200), Pool(200,100)), Wallet(20,0), Wallet(0,0))
        program = constant_program(2)
        final, receipts = execute_route(initial, (Trade(0, 'A2B', 10), Trade(1, 'B2A', 'all')), program)
        self.assertEqual(receipts[0].output, F(200,11))
        self.assertEqual(receipts[1].output, F(400,13))
        self.assertEqual(final.trader, Wallet(F(20-10)+F(400,13), 0))
        self.assertGreater(final.trader.a, initial.trader.a)
        self.assertEqual(_totals(initial), _totals(final))
        self.assertEqual(final.pools[0].k, initial.pools[0].k)
        self.assertEqual(final.pools[1].k, initial.pools[1].k)
        with self.assertRaisesRegex(ValueError, 'not initially balanced'):
            baseline_gap(initial, final, (1,1))

    def test_shared_equilibrium_across_two_pools(self):
        initial = Market((Pool(100,100), Pool(200,200)), Wallet(30,0), Wallet(0,0))
        final, _ = execute_route(initial, (Trade(0,'A2B',10), Trade(1,'B2A','all')),constant_program(2))
        ledger = baseline_gap(initial, final, (1,1))
        self.assertLess(final.trader.a, initial.trader.a)
        self.assertEqual(ledger['hook_drawdown'], 0)
        self.assertGreater(ledger['displacement_gap'], 0)
        self.assertEqual(ledger['invariant_growth_gap'],0)
        self.assertEqual(ledger['trader_gain'], -ledger['displacement_gap'])

    def test_funded_hook_can_create_profit_bounded_by_its_budget(self):
        initial = Market((Pool(100,100), Pool(200,200)), Wallet(20,0), Wallet(0,5))
        phase0 = ((HookRule(1,0, 'B', 5), HookRule(1,0)),
                  (HookRule(1,0), HookRule(1,0)))
        program = HookProgram((phase0,))
        end, rs = execute_route(initial, (Trade(0,'A2B',10),Trade(1,'B2A','all')),program)
        assert rs[0].hook_transfer == 5
        self.assertEqual(end.hook,Wallet(0,0))
        self.assertGreater(end.trader.a,20)
        self.assertEqual(end.trader.b,0)
        ledger = baseline_gap(initial,end,(1,1))
        self.assertEqual(ledger['hook_drawdown'],5)
        self.assertGreater(ledger['displacement_gap'],0)
        self.assertEqual(ledger['trader_gain'],end.trader.a-20)
        self.assertLess(ledger['trader_gain'],5)
        self.assertEqual(ledger['invariant_growth_gap'],0)

    def test_hook_funding_constraint_is_atomic(self):
        initial = Market((Pool(100,100),), Wallet(10,0), Wallet(0,3))
        p = HookProgram((((HookRule(1,0,'B',4),HookRule(1,0)),),))
        with self.assertRaisesRegex(ValueError,'nonnegative'):
            execute(initial, Trade(0,'A2B',5),p)
        self.assertEqual(_totals(initial), Wallet(110,103))

    def test_dynamic_fee_phase_order_is_noncommutative(self):
        initial = Market((Pool(100,100), Pool(200,200)),Wallet(40,0), Wallet(0,0))
        p=program_two_phase(2)
        forward=(Trade(0,'A2B',10),Trade(1,'A2B',10))
        reverse=(Trade(1,'A2B',10),Trade(0,'A2B',10))
        x,rx=execute_route(initial,forward,p)
        y,ry=execute_route(initial,reverse,p)
        self.assertEqual(x.phase,y.phase)
        self.assertEqual(x.trader.a,y.trader.a)
        self.assertNotEqual(x.trader.b,y.trader.b)
        self.assertEqual((rx[0].gamma,rx[1].gamma),(F(1), F(1,2)))
        self.assertEqual((ry[0].gamma,ry[1].gamma),(F(1), F(1,2)))
        for final in (x,y):
            ledger=baseline_gap(initial,final,(1,1))
            self.assertLess(ledger['trader_gain'],0)
            self.assertGreaterEqual(ledger['invariant_growth_gap'],0)

    def test_nonincreasing_k_and_wealth_bound_exhaustive_grid(self):
        fees = (F(1),F(9,10),F(1,2))
        for a0 in (20,35):
            for b0 in (20,35):
                for x in (F(1),F(4)):
                    for y in (F(1),F(4)):
                        for g1 in fees:
                            for g2 in fees:
                                initial=Market((Pool(a0,b0),Pool(2*a0,2*b0)),Wallet(50,0),Wallet(0,0))
                                p=HookProgram((((HookRule(g1,0),HookRule(g1,0)),
                                                  (HookRule(g2,0),HookRule(g2,0))),))
                                end,receipts=execute_route(initial,(Trade(0,'A2B',x),Trade(1,'A2B',y)),p)
                                self.assertEqual(_totals(initial), _totals(end))
                                self.assertTrue(all(r.reserve_k_after>=r.reserve_k_before for r in receipts))
                                ledger=baseline_gap(initial,end,(b0,a0))
                                self.assertEqual(ledger['trader_gain'],
                                                 -ledger['displacement_gap']-ledger['invariant_growth_gap'])
                                self.assertLessEqual(ledger['trader_gain'],0)

    def test_negative_hook_payment_collects_prepaid_fees(self):
        initial=Market((Pool(100,100),),Wallet(20,0),Wallet(0,0))
        p=HookProgram((((HookRule(F(1),0,'A',-2),HookRule(1,0)),),))
        end,_=execute(initial,Trade(0,'A2B',10),p)
        self.assertEqual(end.hook,Wallet(2,0))
        ledger=baseline_gap(initial,end,(1,1))
        self.assertEqual(ledger['hook_drawdown'],-2)
        self.assertLess(ledger['trader_gain'],-2)

    def test_bounded_exact_optimizer_recovers_cross_pool_profit(self):
        initial=Market((Pool(100,200),Pool(200,100)),Wallet(20,0),Wallet(0,0))
        p=constant_program(2)
        choices=(Trade(0,'A2B',10),Trade(0,'B2A','all'),Trade(1,'B2A','all'),
                 Trade(1,'A2B',10))
        result=optimal_route(initial,p,choices,2,(1,1),terminal=lambda s:s.trader.b==0)
        self.assertEqual(result.final_state.trader.b,0)
        self.assertGreater(result.final_value,20)
        self.assertEqual(result.route,(choices[0],choices[2]))
        self.assertGreater(result.explored_states,1)
        with self.assertRaises(ValueError):
            optimal_route(initial,p,(Trade(0,'A2B',10),),1,(1,1),
                          terminal=lambda s:s.trader.b>0 and s.trader.a<0)

    def test_general_budget_perfect_squares_exact(self):
        initial=Market((Pool(100,225),Pool(225,100)),Wallet(50,0),Wallet(0,0))
        final,_=execute_route(initial,(Trade(0,'A2B',10),Trade(1,'B2A','all')),
                              constant_program(2))
        result=general_budget(initial,final,(1,1))
        self.assertEqual(result['initial_mispricing_surplus_upper'],50)
        self.assertGreater(result['trader_gain'],0)
        self.assertLess(result['trader_gain'],50)

    def test_general_budget_certified_sqrt_floor(self):
        for n in range(1,70):
            x=F(n*7, n+1)
            low=lower_sqrt_rational(x,1000)
            self.assertLessEqual(low*low,x)
            self.assertGreater((low+F(1,1000))**2,x)
        with self.assertRaises(ValueError):
            lower_sqrt_rational(2,0)
        with self.assertRaises(ValueError):
            lower_sqrt_rational(-1)

    def test_general_budget_across_pool_ratios_and_fees(self):
        for a in (10,20,50):
            for b in (15,35):
                for c in (20,60):
                    for fee in (F(1), F(9,10), F(3,4)):
                        initial=Market((Pool(a,b),Pool(c,17)),Wallet(20,0),Wallet(0,0))
                        final,_=execute_route(initial,(Trade(0,'A2B',5),Trade(1,'B2A','all')),
                                              constant_program(2,fee))
                        estimate=general_budget(initial,final,(1,1),10000)
                        self.assertLessEqual(estimate['trader_gain'],
                                             estimate['trader_gain_upper'])

    def test_search_cap_and_negative_cases(self):
        initial=Market((Pool(100,100),),Wallet(20,0),Wallet(0,0))
        p=constant_program(1)
        with self.assertRaises(RuntimeError):
            optimal_route(initial,p,(Trade(0,'A2B',1),),2,max_states=1)
        with self.assertRaises(TypeError):
            Trade(0,'A2B',0.25)
        with self.assertRaises(ValueError):
            Trade(0,'A2B',0)
        with self.assertRaises(ValueError):
            HookRule(F(11,10),0)
        with self.assertRaises(ValueError):
            HookProgram((((HookRule(1,2),HookRule(1,0)),),))


if __name__ == '__main__':
    unittest.main()
