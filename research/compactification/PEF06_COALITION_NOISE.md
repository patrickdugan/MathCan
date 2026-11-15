# PEF-06: three-paper synthesis and kernel-checked coalition/noise examples

The new model combines the themes of three **separate** OpenAI math preprints:

1. [Sharp binary-information contraction on the discrete cube](https://github.com/openai/math/blob/main/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/main.pdf), September 24, 2026.
2. [Average sensitivity of polynomial threshold functions](https://github.com/openai/math/blob/main/preprints/Average-Sensitivity-of-Polynomial-Threshold-Functions-September-25-2026/main.pdf), September 25, 2026.
3. [A superquadratic separation between sensitivity and block sensitivity](https://github.com/openai/math/blob/main/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/paper.pdf), September 25, 2026.

The finite algebra and exact oracles below are **independent toy results**.
None of the three broad theorems is imported as a Lean axiom or
claimed to have been reproved.

For each m>=1, the coalition latch is F_m(x)=XOR over j of
(x_(2j) AND x_(2j+1)) on 2m binary inputs.

At all zero, every individual-bit flip has no effect. The m
disjoint complete pairs are sensitive blocks and attain local
block sensitivity m: every intervention changing F_m(0) must
contain at least one full pair, so disjoint sensitive interventions
must use distinct pairs. The global maximum singleton sensitivity
is 2m, and its **uniform average singleton sensitivity is m**,
because each bit is pivotal exactly when its partner is 1.
This family does not give the superquadratic *global*
sensitivity separation in the third paper.

The sign of -product_j(1-2*x_(2j)*x_(2j+1)) is a
polynomial-threshold representation of degree at most 2m,
consistent with the second paper's general average-sensitivity
bound. PEF-06's exact value m is elementary and sharper for
this particular family.

With independent Bernoulli(p) bit-flip noise Z starting from all
zero, each complete AND pair activates with probability p².
Their XOR has exact activation probability

    Q_m(p)=[1-(1-2p²)^m]/2.

The general finite Boolean Möbius expansion is

    E[f(x XOR Z)] = sum_(S subset [n]) D_S f(x) p^|S|,
    D_S f(x) = sum_(T subset S) (-1)^(|S|-|T|)
                               f(x XOR indicator(T)).

At zero, the latch has nonzero coefficients only in even
degrees, c_(2j)=(-1)^(j+1)*2^(j-1)*C(m,j). The leading
term is m*p². For m=3 the polynomial is
3p²-6p⁴+4p⁶; Q_3(1/4)=169/1024.

With X uniform and Y=X XOR Z, output disagreement is

    Pr(F_m(X)!=F_m(Y))=[1-(1-p)^(2m)]/2.

The original and noisy output signs have equal mean 2^(-m)
and pair correlation (1-p)^(2m). Their exact joint law is

    P(F(X)=a,F(Y)=b) =
      [1+(-1)^a*2^(-m)+(-1)^b*2^(-m)
       +(-1)^(a+b)*(1-p)^(2m)]/4.

For m=3,p=1/4 this is P00=5849/16384,
P01=P10=3367/16384, P11=3801/16384.
The uniform-source mismatch is 3367/8192.

By data processing, information in the one-bit noisy
output is at most information in the entire noisy input.
The first preprint's universal one-coordinate contraction
bound concerns the latter and remains a general result
outside the formalized PEF-06 examples.

## Formal scope

MathCan/CoalitionNoise.lean proves, in the Lean kernel:
- six singleton flips leave F_3(0) unchanged;
- three disjoint two-bit flips change it;
- every sensitive intervention contains a complete pair;
- total uniform singleton sensitivity is 192 over 64 inputs;
- at noise p=1/4 the weighted zero-source activation numerator
  equals 676 over 4096 for m=3, and 30 over 256 for m=2;
- two-pair uniform noisy-output disagreement numerator is
  1400 over 4096, yielding 175/512;
- the m=3 closed Möbius polynomial's rational numerator is 676.

General all-m formulas and information calculations are
derived algebraically and independently checked using exact
Fractions and exhaustive source enumeration in
[Compactification-Theory PEF-06](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/pef06-three-paper-coalition-noise-20261115/research/precision_entropy_frontier).

The applied LoopedTransformers frozen-checkpoint gym measures
natural single and joint history interventions separately.
It does not assume a trained network implements F_m.

Reproduce:

    lake build MathCan
    lake env lean MathCan/CoalitionNoise.lean
    python -m unittest discover -s tests -p test_coalition_noise.py -v
