# ACE-03Y-03: Composed exact relativized Choice bridge

The original ZF kernel checks a closed conditional theorem with two antecedents:

1. The exact bounded two-parameter selector Separation instance relativized to L.
2. For every constructible carrier A, existence of an ambient well-order relation R on A such that R belongs to L.

The conclusion is the exact relativized Choice axiom. Prior transitivity and Union closure proofs are rebuilt and inserted as closed proof trees. They are not external assumptions. The two new proof generators expose optional proof-object output while retaining byte-identical default receipts. The final composition imports them through the original checker, checks the guarded formula, and checks its exact expansion by the pinned L definition.

## Checks
- ambient_transitivity: 2897 kernel visits
- class_transitivity: 2911 kernel visits
- ambient_union_closure: 11522 kernel visits
- relativized_union: 14483 kernel visits
- composed_conditional: 110515 kernel visits
- expanded_conditional: 110516 kernel visits
- 5 rejection controls.
- 2 earlier receipts reproduced.
- Zero Choice imports. The original checker accepts the fully expanded closed conditional formula in ZF mode.

## Compiler boundary

The selector formula plus carrier membership has four free variables and needs 10 total slots and 74 instructions under the current lowering convention. The existing compiler cap is six slots and twenty instructions. The two-parameter Separation wrapper also needs to be generalized. Merely changing the caps is not a verified closure proof; a modular formula compiler or an equivalent fixed derivation is needed. The other remaining obligation is internality of a suitable order witness (e.g. by constructing canonical histories within L and transporting them). This checkpoint does not establish an unconditional Choice import.
