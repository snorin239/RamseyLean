# Formalization of *Optimizing the CGMS upper bound on Ramsey numbers*

This document describes the Lean 4 + Mathlib formalization of Gupta, Ndiaye,
Norin, and Wei, [*Optimizing the CGMS upper bound on Ramsey
numbers*](paper/main.pdf). The bundled PDF is the source for all statement
wording and numbering in this document.

The paper supplies the mathematical intent; the declarations accepted by Lean
are the checked statements.

## Targets and dependency structure

The formalization has two public targets:

| Result in `paper/main.pdf` | Lean declaration | Module |
|---|---|---|
| Theorem 1 | `RamseyLean.main` | `RamseyLean/Main.lean` |
| Corollary 6 | `RamseyLean.ramseyNumber_le_easy_optimized` | `RamseyLean/EasyBound.lean` |

`RamseyLean.main` uses one error function `η : ℕ → ℝ`, independent of `ℓ`,
with `η(k) = o(k)`. This is the uniform meaning of the error term specified
after Theorem 1. The coefficients printed as decimals are represented by the
exact rationals `1/4`, `3/100`, and `2/25`.

`RamseyLean.ramseyNumber_le_easy_optimized` preserves the printed statement of
Corollary 6. Its `ℓ`-indexed power is a natural power, while the exponent
`k/2` is implemented by `Real.rpow`. Explicit real casts and the hypotheses
`0 < ℓ`, `ℓ ≤ k` are formal bookkeeping.

The proof has six main stages:

1. `Coloring`, `Counting`, `Ramsey`, and `Candidate` define red-blue
   colorings, crossing-edge counts, density and excess, finite Ramsey bounds,
   the least Ramsey number, and nonempty disjoint candidates.
2. `EasyBound` proves the excess-averaging and candidate-induction arguments,
   then optimizes the density parameter to obtain Corollary 6.
3. `Analysis/Binomial`, `BlueBook`, `Asymptotics/Uniform`, and
   `AsymptoticRegion` provide generalized binomial estimates, blue-book
   extraction, explicit uniform error witnesses, and the asymptotic region.
4. `BookInduction` and `Descent` prove the moment induction, its dense-coloring
   consequence, and the general dense/sparse descent theorem.
5. `Frontier`, `Analysis`, and `Numerics` construct the improved frontier and
   verify two independently optimized numerical descents with exact interval
   certificates.
6. `Main` combines the final exponential bound with a uniform one-sided
   Stirling estimate to obtain the binomial form of Theorem 1.

## Paper-to-Lean map

| Result in `main.pdf` | Lean declaration(s) | Role or difference |
|---|---|---|
| Lemma 2 | `sum_excess_redNeighborhood_ge` | Excess averaging; the square identity proves a slightly stronger unrestricted inequality. |
| Observation 3 | `ramseyBound_erdosSzekeres` | Weighted Erdős--Szekeres bound from the Ramsey recurrence. |
| Lemma 4 | `Candidate.isGood_of_excess_ge` | Candidate induction, stated in a form that branches directly on the two child thresholds. |
| Theorem 5 | `ramseyBound_easy` | Floor-stable parameterized Ramsey bound. |
| Corollary 6 | `ramseyNumber_le_easy_optimized` | Exact public target after parameter substitution. |
| Lemma 7 | `sum_density_mul_card_redNeighborhood_ge` | Density-convexity averaging, derived from Lemma 2 with safe empty-set conversions. |
| Fact 8 | `chooseReal_lower_bound_four_fifths` | Sufficient replacement in the stronger parameter regime used by Lemma 9. |
| Lemma 9 | `exists_redClique_or_blueBook` | Blue-book extraction by finite averaging and double counting. |
| Observation 10 | `baseline_mem_asymptoticRegion`, `AsymptoticRegion.lower`, `lower_mem_asymptoticRegionInterior`, `mem_asymptoticRegion_of_uniform_bound` | The four properties of the asymptotic region, with explicit uniform errors. |
| Lemma 11 | `tendsto_bookParameter`, `exists_bookExponent` | Exponent-selection limit. The limit theorem uses only `0 < p` and `μ < 1`; the use-oriented corollary imposes the paper's unit-interval assumptions and selects a natural exponent `r ≥ 2` for Lemma 12. |
| Lemma 12 | `Candidate.isGood_of_density_card_product` | Main moment/book induction with the paper's parameter conditions; `𝓡_*` is represented by `asymptoticRegionInterior`, and the cutoff is graph-independent. |
| Theorem 13 | `ramseyBound_of_redDensity` | Dense-coloring consequence, generalized to any finite vertex type. |
| Claim 14.1 | `dense_case_uniform` | One density slack and cutoff obtained uniformly by compactness. |
| Theorem 14 | `uniformRamseyExpBound_of_descent` | General dense/sparse descent with an explicit derivative function. |
| Lemma 15 | `frontier_mem_asymptoticRegion` | Piecewise frontier from concavity, symmetry, and explicit range hypotheses. |
| Lemma 16 | `preliminaryNormalizedSlack_pos`, `uniformRamseyExpBound_preliminary`, `FinalCertificate.finalNumericalCertificate`, `uniformRamseyExpBound_final` | Independently reoptimized, kernel-checked replacement for the printed numerical certificate. |
| Theorem 1 | `main_uniform`, `main` | Final uniform-error composition and exact polynomial-exponential correction. |

## Main proof-route differences

- A two-coloring is a `SimpleGraph`: adjacency is red and adjacency in the
  complement is blue. `RamseyBound` is proved first, and `ramseyNumber` is
  then defined as the least bound.
- The random bipartition in the proof of Theorem 5 is replaced by a
  deterministic signed-weight cut induction proving the same finite average.
- The generalized binomial coefficient is Mathlib's descending Pochhammer
  polynomial divided by `b!`. Instead of formalizing the full statement of
  Fact 8, the development proves the stronger-hypothesis estimate actually
  needed for Lemma 9.
- The proof of Lemma 12 uses a one-shot degree-regularized core rather than
  iterative deletion.
- For Theorem 13, a quantitative excess bipartition replaces the balanced
  maximum-density cut. The fixed loss is absorbed by perturbing an interior
  asymptotic-region coordinate.
- Theorem 14 stores every `o(k)` term as an explicit witness. Its dense case
  freezes local parameters and uses a finite subcover to obtain one density
  slack and cutoff; its sparse case includes exact small-ratio and rounding
  arguments.
- Lemma 15 represents the manuscript's endpoint-range language by explicit
  preimage hypotheses. This avoids extending the frontier function or its
  derivative to zero.
- The final Stirling step proves only the one-sided binomial-entropy estimate
  needed for Theorem 1. Its explicit error is `log k / 2 + 2 = o(k)`.

These are proof-route or interface changes. They do not add hypotheses to
Theorem 1 or Corollary 6.

## Certified numerical optimization

The formalization does not translate or trust the manuscript's
Mathematica-assisted certificate. The optimization was redone in two stages:

- the preliminary stage uses `preliminaryB = 3/40` and
  `preliminaryM r = r * exp (-(9/10) * r - (1/20) * r^2)`;
- the final stage uses `finalB = 3/100` and
  `finalM r = r * exp (-(7/10) * r - (13/50) * r^2)`.

Removable singularities are normalized analytically. Proved Taylor enclosures
for exponential and logarithmic expressions feed outward-rounded fixed-point
interval arithmetic at scale `10^12`. The preliminary certificate contains
2,376 positive cells plus a separate origin case; the final certificate
contains 10,227 rows in 415 chunks.

All interval endpoints and checker decisions are exact integers. Floating-point
sampling was used only to select parameters and meshes, not as proof evidence.
The interval operations, analytic enclosures, mesh coverage, and the final
inequalities all have Lean soundness proofs.

## Scope

The formalization covers Theorem 1 and Corollary 6 and the intermediate
results needed for them. Remark 17, including its preliminary unverified
further optimization, and Section 5 (Observation 18 through Remark 22) are not
formalized.

## Verification

The project pins Lean and Mathlib to `v4.32.1`. `RamseyLean.lean` imports the
complete construction and both public results.

- `lake build` succeeds for the complete source tree, including the numerical
  certificate modules.
- The Lean sources contain no `sorry`, `admit`, or user-declared placeholder
  axioms.
- `#print axioms RamseyLean.main` and
  `#print axioms RamseyLean.ramseyNumber_le_easy_optimized` report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No external numerical output is part of the trusted proof.
