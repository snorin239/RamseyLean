# Formalization blueprint

This file is the paper-to-Lean map for the project. The paper supplies the
mathematical intent; declarations accepted by Lean are the trusted result.

## Source snapshot

- Title: *Optimizing the CGMS upper bound on Ramsey numbers*.
- Authors: Parth Gupta, Ndiamé Ndiaye, Sergey Norin, and Louis Wei.
- Canonical source: [`paper/main.tex`](../paper/main.tex).
- Rendered copy: [`paper/main.pdf`](../paper/main.pdf).
- Bibliography/style: [`paper/snorin2.bib`](../paper/snorin2.bib) and
  [`paper/halpha.bst`](../paper/halpha.bst).
- Snapshot recorded: 2026-08-13. The manuscript itself declares no date or
  version identifier.
- `main.tex` SHA-256:
  `B137CF708C561373C7AEE225ECEBC8BD5AF9B4221EFC593D2E950B4239E052F1`.
- `main.pdf` SHA-256:
  `DFACA5B315B19BB4050B6F1C86D5C0D7B1F543C62E88D293690BC36FE591100F`.

If the paper changes, update this section, the inventory, and the checksums in
[`paper/README.md`](../paper/README.md) in a paper-only commit.

## Scope and trust boundary

The completed formalization has two public theorem targets:

1. **Primary target:** `t:main`, with exactly the paper's uniform asymptotic
   meaning described below.
2. **Second target:** `c:easy`, with the printed mathematical statement
   unchanged (apart from explicit Lean casts, positivity hypotheses, and
   `Real.rpow` notation).

Only definitions and intermediate results needed for these targets are in
scope. Paper labels remain a dependency roadmap, but their formal counterparts
may be generalized, weakened, strengthened, split, combined, or replaced when
that materially simplifies the two targets. Every difference and its purpose
must be recorded here and in the declaration docstring.

The entire Multicolor section, all of `r:final`, and the final contextual
remark are explicitly out of scope. The printed `lem:numerics` margins are
also not independent targets: the optimization will be redone for the
formalization, producing whatever kernel-checked inequalities suffice to prove
`t:main`. Every fact actually used must be proved in Lean or matched to
Mathlib; no manuscript assertion, computer output, or placeholder axiom is
trusted by itself.

## Exact interpretation of the main theorem

The footnote following `t:main` makes its `o(k)` uniform in `1 ≤ ℓ ≤ k`. The
completed theorem therefore exposes one error function, independent of `ℓ`:

```text
∃ η : ℕ → ℝ,
  η =o[atTop] (fun k : ℕ ↦ (k : ℝ)) ∧
  ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
    (ramseyNumber k ℓ : ℝ) ≤
      exp (G ((ℓ : ℝ) / k) * k + η k) * (Nat.choose (k + ℓ) ℓ : ℝ)
```

The finite graph layer uses `RamseyBound`.  At the asymptotic layer, direct
real inequalities for `ramseyNumber` avoid repeated ceiling losses; every
explicit uniform witness has a checked natural-ceiling bridge back to
`RamseyBound`.  Every occurrence of `o(k)` is replaced by one explicit witness
or an equivalent epsilon/eventual predicate.

## Exact interpretation of `c:easy`

The public theorem `ramseyNumber_le_easy_optimized` preserves the printed
corollary:

```text
∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
  (ramseyNumber k ℓ : ℝ) ≤
    4 * (k + ℓ) *
      (((√5 + 1) * (k + 2*ℓ)) / (4*ℓ)) ^ ℓ *
      ((k + 2*ℓ) / k) ^ ((k : ℝ) / 2)
```

All arithmetic on the right is in `ℝ`; the final power is `Real.rpow`.
Explicit coercions and the redundant consequence `0 < k` are formal
bookkeeping, not changes to the mathematical statement.

## Modeling decisions

1. **Two colors.** A red-blue coloring on a finite vertex type `V` is a
   `SimpleGraph V`: adjacency is red and `Gᶜ` adjacency is blue. This reuses
   symmetry, looplessness, complements, neighborhoods, and clique APIs.
2. **Cliques.** A monochromatic clique of exactly `n` vertices uses
   `SimpleGraph.IsNClique n s`. `CliqueFree` and `CliqueFreeOn` are used for
   negated forms.
3. **Ramsey bounds first.** Define `RamseyBound k ℓ N` as the universal
   red/blue clique property on `Fin N`, prove monotonicity, recurrence, and
   existence, and only then define `ramseyNumber` by minimization.
4. **Counting and density.** Reuse `SimpleGraph.interedges` and
   `SimpleGraph.edgeDensity`. The latter is rational; paper expressions are
   coerced to `ℝ`. The local `redInteredgeCount` and `redDensity` interfaces
   hide casts. `interedges X Y` counts ordered pairs, so it agrees with the
   paper's crossing-edge count for disjoint candidate sets. The descent layer's
   `redGraphDensity` uses the degree sum divided by `N(N-1)`, which is the usual
   unordered whole-graph density by handshaking; in particular,
   `redDensity G univ univ` is not that density because its denominator is
   `N²`. Mathlib already assigns local density zero when either finset is empty.
5. **Candidates.** `Candidate G X Y` stores `X.Nonempty`, `Y.Nonempty`, and
   `Disjoint X Y`. Candidate goodness is a separate predicate. Subcandidate
   lemmas must prove nonemptiness rather than silently treating empty sets as
   candidates.
6. **Powers.** Nonintegral real exponents use `Real.rpow`; natural powers keep
   `Pow.pow`. All bases and denominator side conditions are explicit.
7. **Natural parameters.** Paper parameters in `ℕ` that mean positive integers
   carry hypotheses such as `0 < k`, `0 < ℓ`, and `0 < t`. This avoids silently
   assigning meaning to Ramsey numbers or `K_0` outside the paper's scope.
8. **Uniform asymptotics.** Store an explicit error function and a Mathlib
   `IsLittleO` proof at `atTop`. Two-variable statements use a stated filter or
   an epsilon/eventual formulation; no informal `o(k)+o(ℓ)` notation appears in
   a declaration.
9. **Generalized binomial.** Define `chooseReal x b` by evaluating Mathlib's
    root-level `descPochhammer ℝ b` at `x` and dividing by `b!`. Its product
    formula is `∏ i < b, (x - i)`. Prove agreement with `Nat.choose` on
    natural inputs before using convexity or `f:binomial`.
10. **Boundary conventions.** `asymptoticRegion0` uses coordinates in
    `(0,1)²`; `asymptoticRegion` is its closure in `ℝ × ℝ`, so boundary points
    may occur; `asymptoticRegionInterior` is the ambient interior.

## Implemented module graph

| Module | Responsibility | Direct project dependencies |
|---|---|---|
| `RamseyLean/Coloring.lean` | red graph, blue complement, clique and neighborhood interfaces | Mathlib `SimpleGraph` basics |
| `RamseyLean/Counting.lean` | interedge counts, real density, excess, finite sum identities | `Coloring` |
| `RamseyLean/Ramsey.lean` | `RamseyBound`, monotonicity, recurrence, least Ramsey number | `Coloring` |
| `RamseyLean/Candidate.lean` | candidates, goodness, subcandidates | `Counting`, `Ramsey` |
| `RamseyLean/EasyBound.lean` | `l:FpAvg` through `c:easy` | `Candidate` |
| `RamseyLean/Analysis/Binomial.lean` | descending Pochhammer, `chooseReal`, `f:binomial` | Mathlib analysis/choose APIs |
| `RamseyLean/BlueBook.lean` | blue books and `l:BBook` | `Candidate`, `Analysis/Binomial` |
| `RamseyLean/Asymptotics/Uniform.lean` | explicit uniform-error predicates and closure lemmas | `Ramsey` |
| `RamseyLean/AsymptoticRegion.lean` | `𝓡₀`, `𝓡`, `𝓡_*`, `o:r` | `EasyBound`, `Asymptotics/Uniform` |
| `RamseyLean/BookInduction.lean` | `l:FpAvg2`, `l:limit`, `t:bookmain` | `BlueBook`, `AsymptoticRegion` |
| `RamseyLean/Descent.lean` | `t:bookCor`, `c:gen`, `t:general` | `BookInduction` |
| `RamseyLean/Frontier.lean` | frontier construction and `lem:frontier` | `AsymptoticRegion` |
| `RamseyLean/Analysis/CertifiedNumerics.lean` | analytic Taylor enclosures for `exp` and `log` | Mathlib elementary analysis |
| `RamseyLean/Analysis/NormalizedFunctions.lean` | removable-singularity normalizations used near ratio zero | `Analysis/CertifiedNumerics` |
| `RamseyLean/Analysis/FixedPointInterval.lean` | scaled-integer outward-rounded interval arithmetic and soundness theorems | `Analysis/NormalizedFunctions` |
| `RamseyLean/Numerics/Core.lean`, `Ranges.lean` | exact rate functions, retuned parameters, derivatives, concavity, positivity, and unit ranges | `Frontier` |
| `RamseyLean/Numerics/PreliminarySmooth.lean`, `PreliminaryCertificate*.lean`, `Preliminary.lean` | normalized preliminary slack, checked literal interval rows, continuum coverage, and the first descent application | numerical analysis backend, `Descent` |
| `RamseyLean/Numerics/FrontierFacts.lean`, `Final*.lean`, `FinalCertificate*.lean` | explicit preliminary frontier formulas, piecewise approximate final frontier, checked branch meshes, and the concrete final certificate | preliminary descent, `Frontier`, numerical analysis backend |
| `RamseyLean/Numerics.lean` | public assembly of the independently derived final uniform exponential bound | numerical certificate modules |
| `RamseyLean/Main.lean` | uniform binomial-entropy estimate and exact public statement `t:main` | `Numerics`; Mathlib `Stirling` |

This is the implemented module structure; every listed module contains the
declarations described here.

## Definition inventory

| Declaration | Module | Meaning | Status |
|---|---|---|---|
| `hasCliqueOn`, `hasRedClique`, `hasBlueClique` | `Coloring` | exact monochromatic cliques via `IsNClique`; complement is blue | implemented; restriction, clique-free, and neighborhood-extension interfaces compile |
| `redInteredgeCount`, `redDensity` | `Counting` | paper's `e_R(X,Y)` and `d(X,Y)` | implemented; symmetry, empty-set, bounds, density/count conversion, and restricted-neighborhood sums compile |
| `excess` | `Counting` | `e_R(X,Y) - p |X||Y|` in `ℝ` | implemented; symmetry, empty-set, density form, and disjoint-union additivity compile |
| `RamseyBound` | `Ramsey` | universal two-color bound predicate | implemented; finite-set transport, order monotonicity, color symmetry, positive-parameter recurrence, and existence compile |
| `ramseyNumber` | `Ramsey` | least `N` satisfying `RamseyBound` | implemented by `Nat.find`; specification, minimality, bound equivalence, symmetry, and zero/positive boundary lemmas compile |
| `Candidate` | `Candidate` | nonempty disjoint vertex finsets | implemented; side-swap, cardinality, explicit-nonempty subcandidate, and positive excess/density interfaces compile |
| `Candidate.IsGood` | `Candidate` | paper's `(k,ℓ,t)`-good predicate | implemented; enlargement, side-swap, singleton bases, Ramsey-cardinality certificates, and red/blue extension interfaces compile |
| `easyCandidateThreshold` | `EasyBound` | the excess threshold in `l:easy` | implemented in the printed positive-parameter coordinates |
| `easyX`, `easyRamseyBoundValue` | `EasyBound` | the auxiliary density and real bound in `t:easy` | implemented; the checked Ramsey theorem uses a natural-floor interface so it implies the exact real inequality without rounding loss |
| `exists_bipartition_excess_ge` | `EasyBound` | finite bipartition with excess at least the signed-weight cut average | implemented by deterministic vertex induction; replaces the paper's probabilistic phrasing without changing its estimate |
| `BlueBook` | `BlueBook` | blue clique spine and blue cross-edges | implemented; disjointness, spine extraction, clique extension, and the `Candidate.IsGood` lifting interface compile |
| `chooseReal` | `Analysis/Binomial` | generalized real binomial coefficient using Mathlib's descending Pochhammer polynomial | implemented; product formula, natural-input agreement, positivity, and the finite Jensen interface compile |
| `SublinearError`, `UniformRamseyExpWitness` | `Asymptotics/Uniform` | an explicit `o(k)` error and a single witness uniform for `1 ≤ ℓ ≤ k` | implemented; errors compose, rates weaken on `(0,1]`, symmetry and natural-ceiling Ramsey bridges compile |
| `UniformRamseyExpBound`, `EventuallyUniformRamseyExpBound` | `Asymptotics/Uniform` | equivalent explicit-witness and epsilon/eventual forms of `R(k,ℓ) ≤ exp(F(ℓ/k)k+o(k))` | implemented; the converse uses the finite maximum `uniformRamseyLogError` over all admissible `ℓ` |
| `asymptoticRegion0`, `asymptoticRegion` | `AsymptoticRegion` | paper's `𝓡₀` and its closure `𝓡` | implemented; `𝓡₀` uses positive natural parameters and exact natural inverse powers beyond a `k+ℓ` threshold |
| `asymptoticRegionInterior` | `AsymptoticRegion` | paper's ambient interior `𝓡_*` | implemented; interior points are proved to lie back in `𝓡₀`, exposing an actual eventual bound for book induction |
| `bookMoment`, `redRegularCore` | `BookInduction` | the moment invariant and one-shot degree-regularized core used in `t:bookmain` | implemented; `exists_redDegreeRegularized` replaces the paper's iterative deletion while preserving the exact moment and hereditary density |
| `BookSlack`, `BookAsymptoticScaleBounds` | `BookInduction` | graph-independent analytic slack and the logarithmic spine/page schedule estimates | implemented; one cutoff controls the initial loss, blue-book gain, exceptional Ramsey set, and local error |
| `BookInductionData`, `BookInductionBounds`, `concreteBookInductionData` | `BookInduction` | abstract finite induction interface and its concrete realization | implemented; the minimum-left-size floor is absorbed by using the schedule at `ℓ - 1` and increasing the final cutoff by one |
| `redGraphDensity`, `bookCorThreshold` | `Descent` | usual whole-graph red density and the printed square-root order threshold in `t:bookCor` | implemented; whole density uses the degree sum over `N(N-1)`, while the threshold squares to the natural-power product consumed by book induction |
| `denseCaseExponent`, `exists_small_ratio_erdosSzekeres`, `exists_compl_degree_gt_of_redGraphDensity_lt` | `Descent` | logarithmic book rate, exact small-ratio base case, and sparse-branch blue-degree averaging | implemented; these isolate the analytic and graph interfaces used by `c:gen` and `t:general`, with the small-ratio bound valid for every positive parameter pair and no asymptotic cutoff |
| `entropy`, `gPoly`, `g`, `F`, `FSlope`, `FCurvature` | `Numerics/Core` | paper's `h`, `g_b`, and `F_b`, with explicit first and second derivatives | implemented; derivatives, continuity, positivity, positive slope, and strict concavity compile on the exact parameter rectangle |
| `binomialEntropyError`, `uniform_choose_entropy_lower_bound` | `Main` | explicit uniform lower binomial-entropy estimate with logarithmic loss | implemented; global Stirling bounds give the sublinear witness `log k / 2 + 2`, and the one-sided statement is exactly what `t:main` consumes |
| `preliminaryB`, `finalB`, `preliminaryM`, `finalM`, `numericalP`, `numericalX` | `Numerics/Core`, `Numerics/Ranges` | independently chosen descent parameters and the exact `t:general` first coordinate | implemented; `finalB = 3/100` is the coefficient required by `t:main`, and both stages have checked range and continuity interfaces |
| `preliminaryNormalizedSlack`, `finalSmallNormalizedSlack`, `finalMiddleNormalizedSlack`, `finalLargeNormalizedSlack` | `Numerics/PreliminarySmooth`, `Numerics/Final` | smooth one-variable forms of the branchwise descent inequalities | implemented algebraic reductions; concrete interval certificates are recorded separately in the result inventory |
| `FixedPointInterval.Interval`, `FixedPointInterval.Sound` | `Analysis/FixedPointInterval` | exact scaled-integer interval operations, Taylor enclosures, and cast-to-real soundness | implemented; interval endpoints and all checker decisions are exact integers, with outward rounding proved in Lean |
| `frontierA`, `frontierB`, `frontierY` | `Frontier` | functions in `lem:frontier` | implemented; the outer branches choose parameters from explicit level-set preimages, while public branch lemmas expose the resulting equations for numerical use |

## Result inventory

Only `c:easy` and `t:main` are exact public-statement targets. Other rows are
support interfaces; their status notes and declaration docstrings record every
intentional difference from the paper.

| Paper label | Declaration | Module | Direct mathematical dependencies | Status / note |
|---|---|---|---|---|
| `l:FpAvg` | `sum_excess_redNeighborhood_ge` | `EasyBound` | `excess`; interedge double count; sum of squares | implemented; paper hypotheses are retained in the public signature although the square identity proves a stronger unrestricted statement |
| `o:easybound` | `ramseyBound_erdosSzekeres` | `EasyBound` | `RamseyBound` recurrence; induction on `k+ℓ` | implemented as the paper's real inequality for `ramseyNumber` |
| `l:easy` | `Candidate.isGood_of_excess_ge` | `EasyBound` | `l:FpAvg`, `o:easybound`; induction on `k+t` | implemented; branches directly on the two child thresholds, an equivalent strengthening that avoids quotient bookkeeping |
| `t:easy` | `ramseyBound_easy` | `EasyBound` | `l:easy`; deterministic signed-weight bipartition; induction on `ℓ`; algebraic identity `(1-x)(p-x)=(1-p)^2` | implemented in floor-stable form: `⌊easyRamseyBoundValue p k ℓ⌋₊ ≤ N → RamseyBound k ℓ N` |
| `c:easy` | `ramseyNumber_le_easy_optimized` | `EasyBound` | `t:easy`; parameter substitution and real algebra | **implemented exact public target** for positive `ℓ ≤ k`; natural and real powers match the printed statement |
| `l:FpAvg2` | `sum_density_mul_card_redNeighborhood_ge` | `BookInduction` | `l:FpAvg`; interedge double count; density/count conversion | **implemented:** obtained from the excess-averaging inequality at `p = d(X,Y)`, with empty-right-safe conversion helpers |
| `f:binomial` | `chooseReal_lower_bound_four_fifths` | `Analysis/Binomial` | `chooseReal`; elementary descending-product estimate | **implemented as a sufficient replacement:** under the stronger downstream hypothesis `5b² ≤ σm`, the generalized choose is at least `(4/5)σ^b choose(m,b)`; the paper's more general exponential statement is not formalized |
| `l:BBook` | `exists_redClique_or_blueBook` | `BlueBook` | sufficient generalized-choose bound; finite powerset averaging and double counting; Ramsey bound `R(k,m)` | **implemented:** omits the unused candidate right side, rewrites `m ≥ 10μ⁻¹b²` equivalently as `10b² ≤ μm`, and strengthens `b ≤ #S` to `#S = b` |
| `o:r` | `baseline_mem_asymptoticRegion`, `AsymptoticRegion.lower`, `lower_mem_asymptoticRegionInterior`, `mem_asymptoticRegion_of_uniform_bound` | `AsymptoticRegion` | `o:easybound`; closure/interior; Ramsey symmetry; explicit uniform asymptotics | **implemented:** part (4)'s informal two-variable errors are replaced by one uniform-rate witness and its two supporting-line inequalities, exactly the interface needed by `lem:frontier`; `asymptoticRegionInterior_subset_asymptoticRegion0` is an additional downstream bridge |
| `l:limit` | `tendsto_bookParameter`, `exists_bookExponent` | `BookInduction` | `Real.log`, `Real.rpow`, standard limits | **implemented and generalized** to arbitrary `0<p<1`, `0<μ<1`; the use-oriented corollary selects a natural `r ≥ 2` with `p^(1/r)>μ` and the required strict bound |
| `t:bookmain` | `Candidate.isGood_of_density_card_product` | `BookInduction` | `exists_bookSlack`, `BookAsymptoticScaleBounds`, `o:r(3)`, `l:BBook`, `l:FpAvg2`, `ramseyNumber_le_pow_first`; strong induction on `k+t` | **implemented:** the cutoff is chosen before the graph and vertex type, hence is graph-independent; the formal theorem strengthens the printed statement by omitting the unnecessary hypothesis `p>μ₀` |
| `t:bookCor` | `ramseyBound_of_redDensity` | `Descent` | strengthened `t:bookmain`; quantitative excess bipartition; openness of `𝓡_*` | **implemented:** the graph-local theorem is generalized from `Fin N` to any finite vertex type and keeps the printed density and real order hypotheses; instead of the paper's balanced maximum-density cut, it applies `exists_bipartition_excess_ge` at a nearby `p₀ < p`, whose positive excess forces a constant-fraction candidate product, then absorbs that fixed loss by perturbing `y` upward inside `𝓡_*` |
| `t:general` | `uniformRamseyExpBound_of_descent` | `Descent` | `c:gen`, `t:bookCor`; compactness; weighted Erdős--Szekeres; mean value theorem; strong induction on `ℓ` | **implemented:** the formal statement represents `F'` by an explicit continuous-on-`(0,1]` slope function `D` and `HasDerivAt F (D r) r`, represents the positive codomain of `F` by pointwise nonnegativity, and retains the agreed `ContinuousOn M (Ioc 0 1)` hypothesis; `exists_small_ratio_erdosSzekeres` handles small ratios exactly, while compact uniform continuity of `D`, `exists_compl_degree_gt_of_redGraphDensity_lt`, and a floor-stable mean-value estimate implement the sparse blue-neighborhood induction |
| `c:gen` | `dense_case_uniform` | `Descent` | `t:bookCor`; compact finite subcover; perturbation from `𝓡` to `𝓡_*` | **implemented and graph-generalized:** `D` is an explicit slope function and the theorem works on any finite vertex type; each ratio chooses frozen nearby book parameters, a relative neighborhood, and a local cutoff, after which a finite subcover supplies one positive density slack and one cutoff; this avoids the manuscript's unproved uniform perturbation of `M` and additionally returns `2δ < D(r)` uniformly |
| `lem:frontier` | `frontier_mem_asymptoticRegion` | `Frontier` | `o:r(4)`; Ramsey symmetry; strict concavity and range hypotheses | **implemented:** `concaveOn_le_tangentLine` supplies the supporting-line estimate, the two parametric outer points and the hyperbolic middle segment are proved separately, and the printed piecewise `frontierY` is assembled using direct preimage hypotheses formalizing the manuscript's informal endpoint-range language |
| `lem:numerics` | `preliminaryNormalizedSlack_pos`, `uniformRamseyExpBound_preliminary`, `FinalCertificate.finalNumericalCertificate`, then `uniformRamseyExpBound_final` | split `Numerics` modules | exact formulas; kernel-checked analytic and interval inequalities; two applications of `t:general` | **implemented by an independent replacement:** 2,376 preliminary positive-cell rows plus the origin row and 10,227 final rows are checked through proved fixed-point interval soundness; both descent endpoints and the public final uniform bound compile |
| `t:main` | `main_uniform`, then `main` | `Main` | `uniformRamseyExpBound_final`; `uniform_choose_entropy_lower_bound`; composition of uniform errors | **implemented exact public target:** one error function is uniform for every positive `ℓ ≤ k`, and `main` expands `g finalB` to the printed polynomial-exponential correction |

### Explicitly excluded results

| Paper material | Reason |
|---|---|
| `r:final` in full | outside the requested scope; no endpoint or AI-generated claim will be formalized |
| `o:easybound2`, `l:easy2`, `t:easy2`, `c:easy2` | the entire Multicolor section is outside scope |
| final unlabeled remark about Balister et al. | contextual literature discussion, not a target |

## Dependency milestones

1. **Finite graph interface:** complete. `Coloring`, `Counting`, `Ramsey`, and
   `Candidate` provide the checked complement/clique and interedge identities.
2. **Exact easy target:** complete. The printed statement of `c:easy` is
   exposed as `ramseyNumber_le_easy_optimized` and also seeds `𝓡`.
3. **Book extraction:** complete. The sufficient `chooseReal` bound and the
   downstream blue-book extraction are implemented and checked.
4. **Asymptotic language:** complete. Uniform error witnesses, their
   epsilon/eventual equivalence, the three asymptotic regions, all four parts
   of `o:r`, and the interior-to-eventual-bound bridge are implemented.
5. **Book induction and dense corollary:** complete through `t:bookCor`, including generalized
   exponent selection, density averaging, one-shot degree regularization,
   logarithmic schedules, the finite strong-induction engine, and the
   quantitative-excess descent from a dense whole graph to a candidate.
6. **Descent/frontier:** complete. The support version of `t:general`, including
   `c:gen`, is implemented with the agreed relative continuity hypothesis on
   `M`, and `lem:frontier` provides the piecewise frontier together with
   explicit branch relations for the numerical milestone.
7. **Independent optimization and main theorem:** complete. The independent
   numerical optimization reaches `uniformRamseyExpBound_final`; the global
   Stirling estimate supplies an explicit uniform `O(log k)` binomial-entropy
   loss; `main_uniform` and `main` assemble the exact statement of `t:main`.

Each milestone was checked with focused file checks and `lake build`, with no
`sorry`, `admit`, or new axioms.

## Scope decisions and obligation status

### Resolved decisions

- **G1 — outline prose:** irrelevant to the formalization. The literal
  `INCOMPLETE` at `paper/main.tex:330` belongs only to the informal outline;
  it does not qualify or block the detailed proof that follows.
- **G2 — `p>μ₀`:** the formal `t:bookmain` omits this unnecessary hypothesis.
  The generalized `exists_bookExponent`, valid for arbitrary `0<p<1` and
  `0<μ<1`, supplies a natural `r≥2` with both `p^(1/r)>μ` and the strict
  inequality needed by the moment induction. The theorem docstring records
  that this omission strengthens the printed lemma.
- **Book-induction bookkeeping:** the formal proof replaces the paper's
  iterative deletion with the one-shot `redRegularCore`. Its capped-profile
  argument uses the exact sufficient cutoff
  `μ₀+2ε < (μ₀+ε)/(μ₀+x₀+2ε)`, weaker than the paper's auxiliary cutoff. The
  concrete minimum-left-size is `⌊(1+ε)^(n+ℓ)⌋₊`; estimates at `ℓ-1` and a
  one-step larger final cutoff absorb the floor without changing `t:bookmain`.
- **G3 — regularity of `M`:** the formal `t:general` retains the agreed
  hypothesis `ContinuousOn M (Ioc 0 1)`, so concrete applications must prove
  this relative continuity. The implemented proof is actually stronger: its
  compact finite subcover freezes `M`, `X`, and `Y` separately at each anchor,
  eliminating the manuscript's unsupported uniform perturbation and leaving
  the `M`-continuity hypothesis unused inside `c:gen`.
- **G4 — generalized choose:** `chooseReal` is the root-level Mathlib
  `descPochhammer` evaluation divided by `b!`. The product formula,
  natural-input agreement, positivity, and Jensen interface are implemented.
  Instead of the printed exponential form of `f:binomial`, the development
  proves `chooseReal_lower_bound_four_fifths` under `5b² ≤ σm`, precisely the
  stronger regime available in `l:BBook`. Its `4/5` factor combines with the
  two later `4/5` losses to give `64/125 > 1/2`, so it is sufficient for the
  paper's blue-book conclusion.
- **Frontier range language:** the paper's statements that `A` increases from
  `0` to `A(1)` and `B` decreases from `1` to `B(1)` are represented by the
  exact preimage hypotheses used by the outer branches of `frontierY`, together
  with the pointwise unit-range hypothesis for `B`. Strict concavity and the
  explicit derivative function supply the supporting-line estimates. This
  avoids extending `F` or its derivative to `0` and exposes relational branch
  lemmas for later interval verification.
- **G5 — independent optimization:** resolved without translating the
  manuscript's Mathematica certificate or preserving its preliminary
  constants. The first stage uses `preliminaryB = 3/40` and
  `preliminaryM r = r * exp (-(9/10) * r - (1/20) * r^2)`; the second uses
  the exact target coefficient `finalB = 3/100` and
  `finalM r = r * exp (-(7/10) * r - (13/50) * r^2)`. The frontier branches
  are reduced to exact polynomial, exponential, and hyperbolic formulas.
  Removable singularities are normalized analytically, and proved Taylor
  enclosures feed outward-rounded fixed-point intervals at scale `10^12`.
  The preliminary certificate has 2,376 positive-cell rows plus a separate
  origin row; the final certificate has 10,227 rows in 415 kernel-checked
  chunks. Floating-point sampling chose parameters and meshes only and is not
  proof evidence. The concrete endpoints
  `uniformRamseyExpBound_preliminary`,
  `FinalCertificate.finalNumericalCertificate`, and
  `uniformRamseyExpBound_final` all compile.
- **G6:** all of `r:final` is excluded, so neither its endpoint nor its
  unverified AI-generated improvement is a proof obligation.
- **G7/G8:** the Multicolor section is excluded in full; its typos and omitted
  steps are not proof obligations.
- **G9:** `uniform_choose_entropy_lower_bound` proves the one-sided part of the
  manuscript's uniform Stirling display that is actually used by `t:main`.
  Mathlib's global lower factorial bound and the antitonicity of
  `Stirling.stirlingSeq` give the explicit error
  `binomialEntropyError k = log k / 2 + 2 = o(k)`.  Combining this witness with
  `uniformRamseyExpBound_final` yields `main_uniform` and the printed theorem
  `main`.
- **G10 — boundaries and rounding:** resolved. `ramseyBound_zero_left`,
  `ramseyBound_zero_right`, `ramseyNumber_zero_left`, and
  `ramseyNumber_zero_right` fix the zero-parameter convention, while
  `ramseyNumber_spec`, `ramseyNumber_le`, and `ramseyNumber_le_iff` expose the
  least-bound interface. `redDensity_empty_left` and
  `redDensity_empty_right` fix empty-input density at zero. The closure and
  interior boundary behavior is checked in `AsymptoticRegion`, including
  `asymptoticRegionInterior_subset_asymptoticRegion0`. The floor bridge used by
  `c:easy` and `UniformRamseyExpWitness.ramseyBound_ceiling` together with
  `ramseyBound_of_ceiling_le` handle real bounds versus integer graph orders.
  The public targets retain the paper's positive-parameter hypotheses.

### Active obligations

None within the requested scope.

## Mathlib audit

The pinned Mathlib is `v4.32.1`. No graph Ramsey-number definition or theorem
was found under `Mathlib/Combinatorics`; the local `RamseyBound` layer is needed.
Useful existing APIs include:

- `Mathlib.Combinatorics.SimpleGraph.Basic`: `SimpleGraph`, complement `Gᶜ`,
  `compl_adj`, `neighborSet`, `induce`, and the complete graph.
- `Mathlib.Combinatorics.SimpleGraph.Finite`: `edgeFinset`, `neighborFinset`,
  `mem_neighborFinset`, `neighborFinset_compl`, and `degree`.
- `Mathlib.Combinatorics.SimpleGraph.Clique`: `IsClique`, `IsNClique`,
  `isNClique_iff`, `CliqueFree`, `CliqueFreeOn`, and clique insertion/subset
  lemmas.
- `Mathlib.Combinatorics.SimpleGraph.Density`: `interedges`, `edgeDensity`,
  `mem_interedges_iff`, `card_interedges_add_card_interedges_compl`,
  `edgeDensity_add_edgeDensity_compl`, commutativity, monotonicity, and the
  empty-set density lemmas. `edgeDensity` is `ℚ`, so the project will provide a
  stable `ℝ` coercion interface.
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum`:
  `sum_degrees_eq_twice_card_edges`; cross-edge sum identities still need local
  lemmas.
- `Mathlib.Algebra.Order.Chebyshev`: the root-level lemmas
  `sq_sum_le_card_mul_sum_sq`, `pow_sum_div_card_le_sum_pow`, and
  `sum_div_card_sq_le_sum_sq_div_card` support the square-convexity step in
  `l:FpAvg2`.
- The random bipartition in `t:easy` is formalized instead by a deterministic
  signed-weight cut induction: when a vertex is inserted, place it on the side
  giving the larger of its two crossing contributions. This proves the same
  finite average estimate without a probability-space dependency.
- `Finset`/`Fintype`: finite sums, products, cards, filters, products,
  `powersetCard`, and finite averaging.
- `Mathlib.Combinatorics.Enumerative.DoubleCounting`:
  `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` identifies the
  total number of blue-book pages counted by spines and by page vertices in
  `l:BBook`.
- `Mathlib.Analysis.SpecialFunctions.Pochhammer`:
  `convexOn_descPochhammer_eval` and especially
  `descPochhammer_eval_div_factorial_le_sum_choose` give the Jensen inequality
  for `chooseReal`. The formal replacement for `f:binomial` uses its product
  formula and an elementary finite-product estimate under `5b² ≤ σm`.
- `Nat.choose`, `Nat.descFactorial`,
  `Nat.descFactorial_eq_factorial_mul_choose`,
  `Nat.choose_eq_descFactorial_div_factorial`, and choose bounds. These cover
  natural upper arguments but not the real `chooseReal` required by G4.
- `Real.exp`, `Real.log`, `Real.rpow`, derivative/continuity lemmas, convexity
  APIs, and standard tendsto lemmas for `l:limit`, descent, and frontier work.
- `Mathlib.Analysis.Asymptotics`: `IsLittleO`, notation `=o[atTop]`,
  `isLittleO_iff`, and `isLittleO_iff_tendsto`; use these with an explicit
  error function.  `Finset.sup'` applied to the positive logarithmic Ramsey
  deficits produces a canonical uniform error and proves equivalence with the
  epsilon/eventual formulation.
- `Mathlib.Analysis.SpecialFunctions.Stirling`: `Stirling.stirlingSeq`,
  `Stirling.factorial_isEquivalent_stirling`, and logarithmic/global bounds.
  `Main` derives the missing upper logarithmic factorial bound from
  `Stirling.log_stirlingSeq'_antitone`, combines it with
  `Stirling.le_log_factorial_stirling`, and proves the uniform one-sided
  binomial-entropy corollary required for G9.
- `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`: `Real.binEntropy` has
  continuity, derivative, and strict-concavity support. It may shorten the
  entropy part of the uniform binomial estimate, but no matching
  choose-versus-entropy theorem was found.
- `Set.closure`, `Set.interior`, product topology, compactness, uniform
  continuity, and finite subcover APIs support `𝓡`, `c:gen`, and the frontier.
  The checked `o:r` topology proofs use `map_mem_closure`, `interior_mono`,
  `interior_maximal`, `interior_prod_eq`, and ordered neighborhoods to turn an
  interior point of `closure 𝓡₀` into a point of `𝓡₀` itself.
- `norm_num`, `ring_nf`, `linarith`, `nlinarith`, `positivity`, and exact
  rational inequalities discharge algebraic leaves. The G5 transcendental
  layer uses proved Taylor enclosures for `exp`, `log`, and normalized quotient
  functions, followed by scaled-integer interval arithmetic whose outward
  rounding and cast-to-real soundness are proved in Lean.

Re-run a focused `#check`/`#find` audit in each module before fixing imports;
this inventory records available interfaces, not a promise that every needed
bridge lemma already exists.
