# AHR-08: addressable plaquette curvature

The intact prime hypercube admits a fourth-order local Wilson-loop readout when the initial vertex is the opposite corner of the selected plaquette relative to the phase-controlled edge. A four-phase scan obtains the signed local face curvature at O(t^6) absolute remainder; two-time Richardson cancels its leading relative O(t^2) error. In Q3, three controlled edge locations cover all six faces using 24 phase/initial-state settings.

See AHR08_addressable_plaquette_curvature.md for derivation, sample-complexity scope, Bianchi, and caveats. Run python ahr08_ci.py with NumPy/SciPy for an independent exact-matrix numerical oracle. No QPU, Lean formal proof, or complexity speedup is claimed.