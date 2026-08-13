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

The target is every labeled mathematical result used to prove `t:main`, plus
the paper's elementary multicolor extension. Contextual literature claims are
not formalization targets. In particular:

- `r:final`'s consequence for the verified frontier is in scope after its
  endpoint issue is resolved.
- The unverified ChatGPT-generated polynomial and the claimed diagonal base
  `3.78233...` in `r:final` are explicitly **out of scope**. They must not be
  imported as an axiom, numerical certificate, or consequence of `t:main`.
- The later Balister et al. result in the final unlabeled remark is contextual.
- The Mathematica assertion behind `lem:numerics` is not trusted merely because
  it appears in the paper. The main theorem becomes verified only after those
  inequalities have a kernel-checked Lean proof.
- Cited facts, including `f:binomial`, must be proved in Lean or matched to an
  existing Mathlib theorem; no placeholder axiom is permitted.

## Exact interpretation of the main theorem

The footnote following `t:main` makes its `o(k)` uniform in `1 ≤ ℓ ≤ k`. The
planned theorem must therefore expose one error function, independent of `ℓ`:

```text
∃ η : ℕ → ℝ,
  η =o[atTop] (fun k : ℕ ↦ (k : ℝ)) ∧
  ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
    (ramseyNumber k ℓ : ℝ) ≤
      exp (G ((ℓ : ℝ) / k) * k + η k) * (Nat.choose (k + ℓ) ℓ : ℝ)
```

The foundational version should use `RamseyBound` and a natural ceiling, so
the development does not depend prematurely on constructing the least Ramsey
number. A later equivalence transfers it to `ramseyNumber`. Every other
occurrence of `o(k)` will likewise be replaced by an explicit witness or an
explicit epsilon/eventual predicate.

## Modeling decisions

1. **Two colors.** A red-blue coloring on a finite vertex type `V` is a
   `SimpleGraph V`: adjacency is red and `Gᶜ` adjacency is blue. This reuses
   symmetry, looplessness, complements, neighborhoods, and clique APIs.
2. **Multiple colors.** Use Mathlib's
   `SimpleGraph.TopEdgeLabeling V (Option (Fin c))`, an `EdgeLabeling` of
   `(⊤ : SimpleGraph V)` whose domain is the complete graph's edge set.
   `none` is red and `some i` is blue color `i`; `labelGraph` exposes each
   color to the clique API.
3. **Cliques.** A monochromatic clique of exactly `n` vertices uses
   `SimpleGraph.IsNClique n s`. `CliqueFree` and `CliqueFreeOn` are used for
   negated forms.
4. **Ramsey bounds first.** Define `RamseyBound k ℓ N` as the universal
   red/blue clique property on `Fin N`, prove monotonicity, recurrence, and
   existence, and only then define `ramseyNumber` by minimization.
5. **Counting and density.** Reuse `SimpleGraph.interedges` and
   `SimpleGraph.edgeDensity`. The latter is rational; paper expressions are
   coerced to `ℝ`. The local `redInteredgeCount` and `redDensity` interfaces
   hide casts. Mathlib already assigns density zero when either finset is
   empty.
6. **Candidates.** `Candidate G X Y` stores `X.Nonempty`, `Y.Nonempty`, and
   `Disjoint X Y`. Candidate goodness is a separate predicate. Subcandidate
   lemmas must prove nonemptiness rather than silently treating empty sets as
   candidates.
7. **Powers.** Nonintegral real exponents use `Real.rpow`; natural powers keep
   `Pow.pow`. All bases and denominator side conditions are explicit.
8. **Natural parameters.** Paper parameters in `ℕ` that mean positive integers
   carry hypotheses such as `0 < k`, `0 < ℓ`, and `0 < t`. This avoids silently
   assigning meaning to Ramsey numbers or `K_0` outside the paper's scope.
9. **Uniform asymptotics.** Store an explicit error function and a Mathlib
   `IsLittleO` proof at `atTop`. Two-variable statements use a stated filter or
   an epsilon/eventual formulation; no informal `o(k)+o(ℓ)` notation appears in
   a declaration.
10. **Generalized binomial.** Define `chooseReal x b` by evaluating Mathlib's
    `Polynomial.descPochhammer ℝ b` at `x` and dividing by `b!`. Its product
    formula is `∏ i < b, (x - i)`. Prove agreement with `Nat.choose` on
    natural inputs before using convexity or `f:binomial`.
11. **Boundary conventions.** `asymptoticRegion0` uses coordinates in
    `(0,1)²`; `asymptoticRegion` is its closure in `ℝ × ℝ`, so boundary points
    may occur; `asymptoticRegionInterior` is the ambient interior. The frontier
    function is initially defined only for `0 < x < 1`. Any endpoint extension
    needs a separate limit/closure lemma.

## Planned module graph

| Module | Responsibility | Direct project dependencies |
|---|---|---|
| `RamseyLean/Coloring.lean` | two- and multicolor encodings; color graphs and neighborhoods | Mathlib `SimpleGraph` basics |
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
| `RamseyLean/Numerics.lean` | exact functions and certified slack inequalities | `Frontier` |
| `RamseyLean/Main.lean` | `t:main` and verified part of `r:final` | `Descent`, `Frontier`, `Numerics` |
| `RamseyLean/Multicolor.lean` | multicolor definitions and `o:easybound2` through `c:easy2` | `Coloring`, `Counting`, `Ramsey` |

This is the proposed structure. Create modules only as their first declaration
is implemented; do not add empty scaffolding.

## Definition inventory

| Planned declaration | Module | Meaning | Status |
|---|---|---|---|
| `Multicoloring` | `Coloring` | local abbreviation for Mathlib `TopEdgeLabeling V (Option (Fin c))` | not started |
| `Multicoloring.colorGraph` | `Coloring` | local interface to Mathlib `labelGraph` for red or one blue color | not started |
| `hasRedClique`, `hasBlueClique` | `Coloring` | exact monochromatic cliques via `IsNClique` | not started |
| `redInteredgeCount`, `redDensity` | `Counting` | paper's `e_R(X,Y)` and `d(X,Y)` | not started |
| `excess` | `Counting` | `e_R(X,Y) - p |X||Y|` in `ℝ` | not started |
| `RamseyBound` | `Ramsey` | universal two-color bound predicate | not started |
| `ramseyNumber` | `Ramsey` | least `N` satisfying `RamseyBound`, defined later | not started |
| `Candidate` | `Candidate` | nonempty disjoint vertex finsets | not started |
| `Candidate.IsGood` | `Candidate` | paper's `(k,ℓ,t)`-good predicate | not started |
| `BlueBook` | `BlueBook` | blue clique spine and blue cross-edges | not started |
| `descendingPochhammer`, `chooseReal` | `Analysis/Binomial` | generalized real binomial coefficient | not started |
| `UniformRamseyExpBound` | `Asymptotics/Uniform` | one explicit little-`o` witness uniform in ratios | not started |
| `asymptoticRegion0`, `asymptoticRegion` | `AsymptoticRegion` | paper's `𝓡₀` and its closure `𝓡` | not started |
| `asymptoticRegionInterior` | `AsymptoticRegion` | paper's `𝓡_*` | not started |
| `entropy`, `g`, `F` | `Numerics` | paper's `h`, `g_b`, and `F_b` | not started |
| `frontierA`, `frontierB`, `frontierY` | `Frontier` | functions in `lem:frontier` | not started |
| `multicolorRamseyBound` | `Multicolor` | universal `c+1`-color Ramsey predicate | not started |
| `MulticolorCandidate`, `thetaFactor` | `Multicolor` | multicolor candidates and `Θ(ℓ⃗)` | not started |

## Result inventory

Statuses distinguish a manuscript blocker from ordinary unstarted work. The
declaration names are planned and may change only with a matching blueprint
update.

| Paper label | Planned declaration | Module | Direct mathematical dependencies | Status / note |
|---|---|---|---|---|
| `l:FpAvg` | `sum_excess_redNeighborhood_ge` | `EasyBound` | `excess`; interedge double count; sum of squares | not started; first proof target |
| `o:easybound` | `ramseyBound_erdosSzekeres` | `EasyBound` | `RamseyBound` recurrence; induction on `k+ℓ` | not started |
| `l:easy` | `Candidate.isGood_of_excess_ge` | `EasyBound` | `l:FpAvg`, `o:easybound`; induction on `k+t` | not started |
| `t:easy` | `ramseyBound_easy` | `EasyBound` | `l:easy`; random-bipartition double count; induction on `ℓ`; algebraic identity `(1-x)(p-x)=(1-p)^2` | not started |
| `c:easy` | `ramseyBound_easy_optimized` | `EasyBound` | `t:easy`; parameter substitution and real algebra | not started |
| `l:FpAvg2` | `sum_density_mul_card_redNeighborhood_ge` | `BookInduction` | interedge double count; convexity/Cauchy for squares | not started |
| `f:binomial` | `chooseReal_lower_bound` | `Analysis/Binomial` | `chooseReal`; log/exponential estimates | blocked by G4; cited proof is not imported |
| `l:BBook` | `exists_redClique_or_blueBook` | `BlueBook` | `f:binomial`; finite averaging; Ramsey bound `R(k,m)` | not started after `f:binomial` |
| `o:r` | `baseline_mem_asymptoticRegion`, `AsymptoticRegion.lower`, `lower_mem_asymptoticRegionInterior`, `mem_asymptoticRegion_of_uniform_bound` | `AsymptoticRegion` | `o:easybound`; closure/interior; Ramsey monotonicity; explicit asymptotics | not started |
| `l:limit` | `tendsto_bookParameter` | `BookInduction` | `Real.log`, `Real.rpow`, standard limits | not started; statement may be generalized per G2 |
| `t:bookmain` | `Candidate.isGood_of_density_card_product` | `BookInduction` | `l:limit`, `o:r(3)`, `l:BBook`, `l:FpAvg2`, `R(k,m)≤k^m`; induction on `k+t` | blocked by G1 and G2 |
| `t:bookCor` | `ramseyBound_of_redDensity` | `Descent` | `t:bookmain`; maximum cross-density bipartition; openness of `𝓡_*` | blocked by G2 |
| `t:general` | `uniformRamseyExpBound_of_descent` | `Descent` | `c:gen`, `t:bookCor`; compactness; small-`ℓ` bound; induction on `ℓ` | blocked by G3 and G9 |
| `c:gen` | `dense_case_uniform` | `Descent` | `t:bookCor`; finite parameter net; perturbation from `𝓡` to `𝓡_*` | blocked with `t:general` |
| `lem:frontier` | `frontier_mem_asymptoticRegion` | `Frontier` | `o:r(4)`; Ramsey symmetry; strict concavity and monotonicity | not started |
| `lem:numerics` | `base_slack`, `final_slack` | `Numerics` | exact formulas; certified one-variable inequalities; branch/root isolation | blocked by G5 |
| `t:main` | `main_uniform`, then `main` | `Main` | two uses of `t:general`; `lem:frontier`; `lem:numerics`; positivity/concavity; uniform Stirling estimate | blocked by G5 and G9 after earlier milestones |
| `r:final` | `final_frontier_mem_asymptoticRegion` | `Main` | verified `t:main`; `lem:frontier`; optional endpoint closure lemma | partially in scope; G6; AI claim excluded |
| `o:easybound2` | `multicolorRamseyBound_erdosSzekeres` | `Multicolor` | multicolor Ramsey recurrence; induction on `k+Σℓᵢ` | blocked pending manuscript repair G7 |
| `l:easy2` | `MulticolorCandidate.isGood_of_excess_ge` | `Multicolor` | `l:FpAvg`, `o:easybound2`; induction on `k+Σtᵢ` | not started after G7 |
| `t:easy2` | `multicolorRamseyBound_easy` | `Multicolor` | `l:easy2`; multicolor neighborhood induction; `Θ` decrement inequality; bipartition count | blocked pending G8 |
| `c:easy2` | `multicolorRamseyBound_easy_optimized` | `Multicolor` | `t:easy2`; parameter substitution | not started after G8 |

The final unlabeled remark about Balister et al. is recorded as context only and
receives no Lean declaration.

## Dependency milestones

1. **Finite graph interface:** finish `Coloring`, `Counting`, `Ramsey`, and
   `Candidate`; verify complement/clique and interedge identities.
2. **Easy two-color theorem:** prove through `c:easy`. This gives the first
   end-to-end checked paper result and seeds `𝓡`.
3. **Book extraction:** settle `chooseReal` and `f:binomial`, then prove
   `l:BBook`.
4. **Asymptotic language:** implement uniform error witnesses and prove all
   parts of `o:r` without informal little-`o` notation.
5. **Book induction:** resolve G1/G2 with the authors' intended statement and
   prove `t:bookmain` and `t:bookCor`.
6. **Descent/frontier:** resolve G3/G9, then prove `c:gen`, `t:general`, and
   `lem:frontier`.
7. **Certified numerics and main theorem:** prove `lem:numerics` in the kernel,
   derive `t:main`, and only then add the verified part of `r:final`.
8. **Multicolor branch:** repair G7/G8 and prove the four multicolor results.

Each milestone ends with focused file checks and `lake build`, with no `sorry`,
`admit`, or new axioms.

## Manuscript gaps and required resolutions

- **G1 — incomplete prose.** `paper/main.tex:330` contains the literal marker
  `INCOMPLETE` and a dangling proof-outline sentence in `t:bookmain`; it also
  refers to the proof of `c:easy`, where `l:easy` appears intended. The later
  detailed proof must be audited rather than assuming the outline is complete.
- **G2 — missing parameter hypothesis.** `t:bookmain` assumes `p > μ₀`, but
  `t:bookCor` omits `p > μ` and invokes it. The displayed bound on `x` does not
  imply that inequality. Decide whether to add `p > μ` to the corollary or
  generalize `l:limit` and `t:bookmain`; do not silently strengthen a paper
  statement.
- **G3 — insufficient function regularity.** `t:general` quantifies over
  arbitrary `M,X,Y`, while its proof chooses uniform perturbations involving
  `M` on a compact interval. Add the intended continuity/uniform-away-from-one
  hypotheses, or prove the needed uniform estimate from weaker assumptions.
- **G4 — generalized choose.** `f:binomial` uses `binom(σm,b)` for a real upper
  argument and convexity of `x ↦ binom(x,b)` without defining that function.
  Fix `chooseReal` semantics and the interval on which positivity/convexity is
  used.
- **G5 — numerical certificate.** `lem:numerics` cites Mathematica and lists
  interval/root data but supplies no independently replayable certificate.
  Reconstruct exact rational/Taylor bounds in Lean or add a separately audited
  certificate generator whose output Lean checks.
- **G6 — frontier endpoint and AI claim.** `lem:frontier` defines `Y_f` for
  `0<x<1`, but `r:final` writes `x∈(0,1]`. Supply an endpoint definition and
  closure proof or restrict the claim. The subsequent AI polynomial/base claim
  remains excluded.
- **G7 — malformed multicolor observation.** `o:easybound2` writes
  `x + ∑_{i=1}^c ≤ 1`, omitting `y_i`. Its proof says induction on `ℓ` while
  invoking the case `(k-1,ℓ⃗)`; the intended measure is `k+Σℓᵢ`.
- **G8 — suppressed multicolor steps.** `t:easy2` uses undefined `R` in
  `n ≥ floor R` where `Q` is intended. It also omits the `Θ` decrement
  inequality and most of the bipartition calculation.
- **G9 — uniform asymptotics and Stirling.** Formalize the assertions
  `R(k,ℓ)=e^{o(k)}` for `ℓ=o(k)`, the two-variable error in `o:r(4)`, and
  Stirling uniformly for every `1≤ℓ≤k`. Pointwise asymptotics are insufficient.
- **G10 — boundaries and rounding.** Fix behavior for `k=0`, `ℓ=0`, empty
  finsets, closure boundary coordinates, real thresholds versus integer graph
  orders, floors/ceilings, and the minimum Ramsey number. Paper results will
  carry positive-parameter hypotheses; density remains zero on empty inputs.

## Mathlib audit

The pinned Mathlib is `v4.32.1`. No graph Ramsey-number definition or theorem
was found under `Mathlib/Combinatorics`; the local `RamseyBound` layer is needed.
Useful existing APIs include:

- `Mathlib.Combinatorics.SimpleGraph.Basic`: `SimpleGraph`, complement `Gᶜ`,
  `compl_adj`, `neighborSet`, `induce`, and the complete graph.
- `Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling`:
  `SimpleGraph.EdgeLabeling`, `SimpleGraph.TopEdgeLabeling`, `labelGraph`,
  `TopEdgeLabeling.labelGraph_adj`, `pullback`, and the two-color conversion
  lemmas `toTopEdgeLabeling_labelGraph` and
  `toTopEdgeLabeling_labelGraph_compl`.
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
- `Mathlib.Algebra.BigOperators.Expect`: finite expectation and average
  identities can encode the random bipartition in `t:easy` without a measure
  space.
- `Finset`/`Fintype`: finite sums, products, cards, filters, products,
  `powersetCard`, and finite averaging. Prefer finite double counting over
  introducing probability spaces for random bipartitions.
- `Mathlib.Analysis.SpecialFunctions.Pochhammer`:
  `convexOn_descPochhammer_eval` and especially
  `descPochhammer_eval_div_factorial_le_sum_choose` give the Jensen inequality
  for the proposed `chooseReal`. The exponential lower bound in
  `f:binomial` is still a project lemma.
- `Nat.choose`, `Nat.descFactorial`,
  `Nat.descFactorial_eq_factorial_mul_choose`,
  `Nat.choose_eq_descFactorial_div_factorial`, and choose bounds. These cover
  natural upper arguments but not the real `chooseReal` required by G4.
- `Real.exp`, `Real.log`, `Real.rpow`, derivative/continuity lemmas, convexity
  APIs, and standard tendsto lemmas for `l:limit`, descent, and frontier work.
- `Mathlib.Analysis.Asymptotics`: `IsLittleO`, notation `=o[atTop]`,
  `isLittleO_iff`, and `isLittleO_iff_tendsto`; use these with an explicit
  error function.
- `Mathlib.Analysis.SpecialFunctions.Stirling`: `Stirling.stirlingSeq`,
  `Stirling.factorial_isEquivalent_stirling`, and logarithmic/global bounds.
  A new uniform binomial-entropy corollary is still required for G9.
- `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`: `Real.binEntropy` has
  continuity, derivative, and strict-concavity support. It may shorten the
  entropy part of the uniform binomial estimate, but no matching
  choose-versus-entropy theorem was found.
- `Set.closure`, `Set.interior`, product topology, compactness, uniform
  continuity, and finite subcover APIs support `𝓡`, `c:gen`, and the frontier.
- `norm_num`, `ring_nf`, `linarith`, `nlinarith`, `positivity`, and exact
  rational inequalities can discharge algebraic leaves. They do not by
  themselves certify the transcendental interval claims in G5.

Re-run a focused `#check`/`#find` audit in each module before fixing imports;
this inventory records available interfaces, not a promise that every needed
bridge lemma already exists.
