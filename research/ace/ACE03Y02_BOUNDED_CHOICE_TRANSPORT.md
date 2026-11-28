# ACE-03Y-02: Bounded selector and internal well-order transport

The pinned graph-value predicate is equivalent in pure logic to a bounded predicate: quantify the singleton and unordered-pair witnesses inside the given pair, require the stated coordinates to be members, and bound the remaining universal quantifiers by their sets. This yields an exact bounded two-parameter selector schema. Relativizing the equivalence and applying it to a Separation witness transfers bounded Separation to the exact selector schema of ACE-03Y-01.

The generic transitive-class bounded absoluteness generator proves equivalence between ambient and guarded truth for the bounded Val and selector predicates. Combining it with the pure logical equivalence to the pinned Val gives exact Val absoluteness. For an ambient well-order of a class set with its relation also in the class, transitivity supplies the guards on members and converts the subset premise for class subsets into its ambient counterpart. The ambient least-element theorem supplies a member in the class. Thus the original relativized well-orderability premise follows from ambient well-orders with constructible relation witnesses.

## Verification
- ambient_val_bounded_equivalence: 868 kernel visits
- ambient_selector_bounded_equivalence: 1794 kernel visits
- relativized_val_equivalence: 1093 kernel visits
- relativized_selector_equivalence: 2277 kernel visits
- bounded_val_absoluteness: 4285 kernel visits
- bounded_selector_absoluteness: 17413 kernel visits
- exact_val_absoluteness: 12562 kernel visits
- bounded_separation_to_exact_selector_schema: 4634 kernel visits
- ambient_to_internal_well_order: 88160 kernel visits
- constructible_ambient_orders_to_internal_well_orderability: 88185 kernel visits
- selector_schema_pinned_conversion: 2 kernel visits
- internal_well_orderability_pinned_conversion: 2 kernel visits
- 6 negative controls; no Choice imports.
- Pure logic. Both endpoint conversions checked against pinned L.
- Executed in ECMAScript using the pinned source; independent Node CI is registered.

## Remaining
Prove the exact bounded two-parameter Separation instance (earlier builder restricts parameters to one), and constructibility of a suitable order witness for every constructible carrier. The latter remains the main mathematical obstacle. Relativized Union has its earlier checked certificate. The ambient well-order theorem alone cannot supply membership of the relation in L.
