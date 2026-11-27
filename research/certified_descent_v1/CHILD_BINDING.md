# Indexed-child binding is a separate certificate obligation

ALG-DESCENT-09 companion, 2026-11-27. Synthetic public-witness polynomial routing. The original run aborted at an indexed-child assertion. The guarded replay on spent roots is development evidence, not a new confirmatory result.

## Composition lemma

Let a trusted state registry map each child identity i to an exact object F(i) in a commutative monoid. A parent certificate proposes child identities i_1,...,i_k and concrete factors Q_1,...,Q_k. The route acceptance predicate is the conjunction

    P = product_j Q_j
    Q_j = F(i_j) for every j.

If all accepted child closures certify their registered objects and the local composition rule is sound, induction on a finite well-founded route establishes the root closure. The second condition permits substitution of the certified registered child object into the local product identity. Without it the certificate does not establish that the chosen child identities refer to the factors in that certificate. Product equality may survive permutations or compensating changes among factors; multiplicative equality alone cannot identify an ordered indexed tuple. This is a statement about the typed interface, not a claim that every unbound product is an incorrect factorization.

Example over F_2: A=X^3+X, B=X^3+X^2. These distinct monic cubics agree at every element of F_2. AB=BA=X^6+X^5+X^4+X^3. A proposal (B,A) with fixed expected child tuple (A,B) passes exact parent multiplication, degree and all base-field evaluation fingerprints, yet fails ordered child binding. The toy schoolbook meter charges 20 coefficient operations in both cases. The regression also checks a bound but invalid product and missing child identity.

A prediction head trained on product validity estimates Pr(product valid | public features), whereas a router accepting bound children requires Pr(product valid AND child bound | public features). The former is an upper bound on the latter for the same conditional distribution. Equivalently the difference is the conditional mass of product-valid but unbound proposals. Calibrate and score the actual acceptance predicate; separately report product failures and binding failures. Exact child binding cannot be replaced by a learned probability.

Cache key equivalence must preserve the certified predicate, registry/version scope, and any witness obligations. It need not preserve route costs. A product-valid but unbound proposal must never populate a closure cache. In the public-witness toy registry one may detect a mismatch directly by equality; this is not an algorithm for discovering unknown factors.

## Development audit

V9 independent replay: 100 product-valid but child-unbound candidates among 101,271 eligible candidates; one attempted binding rejection in 1,896 guarded routes. All guarded routes close. The prediction labels remain product-validity labels in V9. New helper and three regression fixtures in DataGoblin PR #89, local tests passed; the original V9 scripts are retained for reproducibility. Full propagation of the joint acceptance target across future generators, labels, teacher values, native cache admission and learned routers remains outstanding. Paper argument only, no Lean verification.
