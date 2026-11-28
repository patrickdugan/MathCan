# VPVNP-02G exact full-domain Walsh rank audit

Registration and 02F repair: 176b383aa9399575fb8be41602ca2af79bf807f5.

The independent integer FWHT of both indicators was evaluated at every dual coefficient, including zero. Direct character enumeration was independently compared for n<=3. All 66,066 dual coefficient matrices agreed with both formulas. Results for each k from 0 to n:

| n | Dual matrices | Full-rank signed sums | Rank-one signed sums |
|---:|---:|---|---|
| 1 | 2 | 1, -1 | 1, -1 |
| 2 | 16 | 6, -2, 2 | 9, 1, -3 |
| 3 | 512 | 168, -24, 8, -8 | 49, 17, 1, -7 |
| 4 | 65,536 | 20160, -1344, 192, -64, 64 | 225, 97, 33, 1, -15 |

This is an exhaustive all-coefficient check, stronger than the previous canonical representative checks at these sizes. It also covers the full-rank and rank-one spectra independently. The committed Python replay will produce the detailed rank counts. Status PASS for the independent exact calculation; Python CI and native check pending.

MatrixRankCharacter.lean proposes native GL trace invariance, reindex transport and reduction to Mathlib's actual rank normal form. This is the arbitrary-dual-rank step, not yet a derivation of the closed formula in the kernel. The remaining formal bridge is to connect the rank-block representative to the actual ordered-frame recurrence and count the rank-one increment character. No extrapolation to a neural circuit lower bound is made.
