# ACE-03Y-01: Exact conditional Choice import

Base: 9056544f354513278e4f25039c4d870bd9462485. The previous checkpoint proves ambient well-orderability. This checkpoint checks the implication from internal well-orderability, relativized Union and one exact selector Separation instance to the kernel's exact relativized disjoint-family Choice axiom.

The ambient Choice proof from ACE-03T has exactly 1 axiom leaf/leaves, all one two-parameter Separation instance. Its formula is the assertion that y is a least element of some member of the family a in the order r. The proof abstracts this schema as a hypothesis; all hypothesis indices are shifted and the resulting closed implication is checked in CL. The bridge takes Union to obtain the carrier, applies well-orderability, and then uses the abstracted Choice lemma. The original compiler relativizes the closed logical implication without importing an axiom. The target is independently reconstructed from the exact source Choice axiom and checked with the unchanged pinned class definition. A cut and a conversion check the exact endpoint under the explicit hypotheses.

## Verification
- prior_ambient_choice: 150 kernel visits
- axiom_abstracted_choice: 151 kernel visits
- source_bridge: 184 kernel visits
- relativized_bridge: 287 kernel visits
- exact_choice_cut: 7 kernel visits
- expanded_choice_conversion: 2 kernel visits
- 7 rejection controls.
- Zero Choice imports. The conditional theorem has empty external context; the final cut has four stated hypotheses.
- The script was executed against the pinned kernel, definition, and proof generator using an ECMAScript runtime. The registered Node replay is the independent CI gate.

## Open obligations
The implication has three explicit antecedents: the exact two-parameter relativized selector Separation schema, the relativized Union axiom (previously checked), and internal well-orderability. The ambient result in ACE-03X does not supply internal well-orderability. The exact selector formula uses the pinned Val formula, whose unrestricted quantifier syntax exceeds the earlier bounded Separation interface. A useful next step is a bounded Kuratowski-pair characterization, enabling a fixed two-parameter bounded Separation certificate. For internal well-orderability, the canonical history must be constructed within L or proved absolute to L with witnesses in L. No claim of an unconditional Choice import, full schema coverage, checker soundness, or native Lean/RH translation is made.
