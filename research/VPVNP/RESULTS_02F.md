# VPVNP-02F local exact results

Registration and 02E repair: 6cb99077a3d4d3c1af613c71bd2dca888ddc9b0a.

Independent exact enumeration tested every ordered independent coefficient system up to ambient dimension three. It checks actual signed fibers, matching prefix multiplicity, and the closed normalized recurrence, with a zero-final-normal control.

| n | Full frames | Independent coefficient systems | Zero-final controls | Off-target cancellations |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 0 |
| 2 | 6 | 9 | 4 | 18 |
| 3 | 168 | 217 | 50 | 1302 |
| total | 175 | 227 | 55 | 1320 |

All comparisons passed. A Python replay implements the same registered conditions and runs in CI. SignedFrameTransport.lean proposes an explicit global sigma-type partition, product-factorization of the signed sum, off-target cancellation, exact cardinal transport and normalized recurrence to the actual restricted kernel-basis average. Native verification is pending. The last identity is a reduction to kernel bases, not yet a theorem about arbitrary dual rank: change of basis and rank-one sampling counts remain outstanding.
