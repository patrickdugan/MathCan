"""CHTR-03 nonlinear comparator: exact-fee constant-product reserve accounting.

A swap is (asset direction, positive input amount, fee multiplier gamma in (0,1]).
The entire input enters the pool; gamma*input is the pricing-effective amount.
The updated reserves and output are exact rational numbers. This excludes
additional hook balance deltas, capital flows and off-pool oracle events.
"""
from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class Pool:
    reserve_a: Q
    reserve_b: Q
    hook_state: int = 0

    def __post_init__(self):
        object.__setattr__(self, 'reserve_a', Q(self.reserve_a))
        object.__setattr__(self, 'reserve_b', Q(self.reserve_b))
        if self.reserve_a <= 0 or self.reserve_b <= 0:
            raise ValueError('strictly positive reserves required')
        if type(self.hook_state) is not int or self.hook_state < 0:
            raise ValueError('invalid hook state')

    @property
    def reserve_product(self):
        return self.reserve_a * self.reserve_b


def swap(pool: Pool, incoming: str, amount, gamma, *, next_state: int | None = None):
    """Return (updated_pool, amount_out) after a fee-only CFMM swap.

    A is pool.reserve_a; B is pool.reserve_b. The return amount is denominated
    in the opposite asset, while the full incoming amount increases reserves.
    """
    amount, gamma = Q(amount), Q(gamma)
    if incoming not in ('A', 'B') or amount <= 0 or not (0 < gamma <= 1):
        raise ValueError('direction A/B, positive input and 0<gamma<=1 required')
    state = pool.hook_state if next_state is None else next_state
    if type(state) is not int or state < 0:
        raise ValueError('invalid next hook state')
    if incoming == 'A':
        x, y = pool.reserve_a, pool.reserve_b
        output = y * (gamma * amount) / (x + gamma * amount)
        later = Pool(x + amount, y - output, state)
    else:
        x, y = pool.reserve_b, pool.reserve_a
        output = y * (gamma * amount) / (x + gamma * amount)
        later = Pool(y - output, x + amount, state)
    assert 0 < output < y
    assert later.reserve_product >= pool.reserve_product
    return later, output


def two_leg_roundtrip(pool: Pool, first_amount, fee_first, fee_second,
                      *, interim_state=1, final_state=0):
    """A->B->A with exact reserve updates and independently chosen fees."""
    after_first, amount_b = swap(pool, 'A', first_amount, fee_first,
                                 next_state=interim_state)
    after_second, amount_a = swap(after_first, 'B', amount_b, fee_second,
                                  next_state=final_state)
    return after_second, amount_a, amount_b
