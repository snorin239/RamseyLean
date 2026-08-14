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

The formalization has two public theorem targets:

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

## Exact interpretation of `c:easy`

The public theorem `ramseyNumber_le_easy_optimized` will preserve the printed
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
   paper's crossing-edge count for disjoint candidate sets; in particular,
   `redDensity G univ univ` is not the usual unordered whole-graph density.
   Mathlib already assigns density zero when either finset is empty.
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

## Planned module graph

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
| `RamseyLean/Numerics.lean` | independently derived optimization and kernel-checked slack inequalities | `Frontier` |
| `RamseyLean/Main.lean` | exact public statement `t:main` | `Descent`, `Frontier`, `Numerics` |

This is the proposed structure. Create modules only as their first declaration
is implemented; do not add empty scaffolding.

## Definition inventory

| Planned declaration | Module | Meaning | Status |
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
| `UniformRamseyExpBound` | `Asymptotics/Uniform` | one explicit little-`o` witness uniform in ratios | not started |
| `asymptoticRegion0`, `asymptoticRegion` | `AsymptoticRegion` | paper's `𝓡₀` and its closure `𝓡` | not started |
| `asymptoticRegionInterior` | `AsymptoticRegion` | paper's `𝓡_*` | not started |
| `entropy`, `g`, `F` | `Numerics` | paper's `h`, `g_b`, and `F_b` | not started |
| `frontierA`, `frontierB`, `frontierY` | `Frontier` | functions in `lem:frontier` | not started |

## Result inventory

Only `c:easy` and `t:main` are exact public-statement targets. Other rows are
support interfaces: their names and statements are provisional and may be
replaced when doing so shortens or clarifies the target proofs, provided this
table and their docstrings record the change.

| Paper label | Planned declaration | Module | Direct mathematical dependencies | Status / note |
|---|---|---|---|---|
| `l:FpAvg` | `sum_excess_redNeighborhood_ge` | `EasyBound` | `excess`; interedge double count; sum of squares | implemented; paper hypotheses are retained in the public signature although the square identity proves a stronger unrestricted statement |
| `o:easybound` | `ramseyBound_erdosSzekeres` | `EasyBound` | `RamseyBound` recurrence; induction on `k+ℓ` | implemented as the paper's real inequality for `ramseyNumber` |
| `l:easy` | `Candidate.isGood_of_excess_ge` | `EasyBound` | `l:FpAvg`, `o:easybound`; induction on `k+t` | implemented; branches directly on the two child thresholds, an equivalent strengthening that avoids quotient bookkeeping |
| `t:easy` | `ramseyBound_easy` | `EasyBound` | `l:easy`; deterministic signed-weight bipartition; induction on `ℓ`; algebraic identity `(1-x)(p-x)=(1-p)^2` | implemented in floor-stable form: `⌊easyRamseyBoundValue p k ℓ⌋₊ ≤ N → RamseyBound k ℓ N` |
| `c:easy` | `ramseyNumber_le_easy_optimized` | `EasyBound` | `t:easy`; parameter substitution and real algebra | **implemented exact public target** for positive `ℓ ≤ k`; natural and real powers match the printed statement |
| `l:FpAvg2` | `sum_density_mul_card_redNeighborhood_ge` | `BookInduction` | interedge double count; convexity/Cauchy for squares | not started |
| `f:binomial` | `chooseReal_lower_bound_four_fifths` | `Analysis/Binomial` | `chooseReal`; elementary descending-product estimate | **implemented as a sufficient replacement:** under the stronger downstream hypothesis `5b² ≤ σm`, the generalized choose is at least `(4/5)σ^b choose(m,b)`; the paper's more general exponential statement is not formalized |
| `l:BBook` | `exists_redClique_or_blueBook` | `BlueBook` | sufficient generalized-choose bound; finite powerset averaging and double counting; Ramsey bound `R(k,m)` | **implemented:** omits the unused candidate right side, rewrites `m ≥ 10μ⁻¹b²` equivalently as `10b² ≤ μm`, and strengthens `b ≤ #S` to `#S = b` |
| `o:r` | `baseline_mem_asymptoticRegion`, `AsymptoticRegion.lower`, `lower_mem_asymptoticRegionInterior`, `mem_asymptoticRegion_of_uniform_bound` | `AsymptoticRegion` | `o:easybound`; closure/interior; Ramsey monotonicity; explicit asymptotics | not started |
| `l:limit` | `tendsto_bookParameter`, `exists_bookExponent` | `BookInduction` | `Real.log`, `Real.rpow`, standard limits | intentionally generalized to arbitrary `0<p<1`, `0<μ<1`; the use-oriented corollary selects a natural `r ≥ 2` with `p^(1/r)>μ` and the required strict bound |
| `t:bookmain` | `Candidate.isGood_of_density_card_product` | `BookInduction` | `exists_bookExponent`, `o:r(3)`, `l:BBook`, `l:FpAvg2`, `R(k,m)≤k^m`; induction on `k+t` | not started; formal statement **omits** printed hypothesis `p>μ₀`, strengthening the lemma as agreed |
| `t:bookCor` | `ramseyBound_of_redDensity` | `Descent` | strengthened `t:bookmain`; maximum cross-density bipartition; openness of `𝓡_*` | not started; can match the printed hypotheses |
| `t:general` | `uniformRamseyExpBound_of_descent` | `Descent` | `c:gen`, `t:bookCor`; compactness; small-`ℓ` bound; induction on `ℓ` | not started; formal statement adds `Continuous M` as agreed |
| `c:gen` | `dense_case_uniform` | `Descent` | `t:bookCor`; finite parameter net; continuity of `M`; perturbation from `𝓡` to `𝓡_*` | not started; may be folded into `t:general` |
| `lem:frontier` | `frontier_mem_asymptoticRegion` | `Frontier` | `o:r(4)`; Ramsey symmetry; strict concavity and monotonicity | not started |
| `lem:numerics` | independently designed optimization lemmas | `Numerics` | exact formulas; kernel-checked analytic or interval inequalities | paper statement replaced by a fresh optimization sufficient for `t:main`; open obligation G5 |
| `t:main` | `main_uniform`, then `main` | `Main` | descent theorem; frontier information; independent optimization; positivity/concavity; uniform Stirling estimate | **primary exact public target**; open obligations G5 and G9 after combinatorial dependencies |

### Explicitly excluded results

| Paper material | Reason |
|---|---|
| `r:final` in full | outside the requested scope; no endpoint or AI-generated claim will be formalized |
| `o:easybound2`, `l:easy2`, `t:easy2`, `c:easy2` | the entire Multicolor section is outside scope |
| final unlabeled remark about Balister et al. | contextual literature discussion, not a target |

## Dependency milestones

1. **Finite graph interface:** finish `Coloring`, `Counting`, `Ramsey`, and
   `Candidate`; verify complement/clique and interedge identities.
2. **Exact easy target:** prove through the printed statement of `c:easy` and
   expose it as `ramseyNumber_le_easy_optimized`. This is the first
   end-to-end target and also seeds `𝓡`.
3. **Book extraction:** settle `chooseReal` and prove `f:binomial`, or replace
   it with a more direct sufficient bound, then prove the blue-book extraction
   needed downstream.
4. **Asymptotic language:** implement uniform error witnesses and prove all
   parts of `o:r` without informal little-`o` notation.
5. **Book induction:** prove the generalized exponent-selection lemma, then
   prove `t:bookmain` without `p>μ₀` and derive `t:bookCor`.
6. **Descent/frontier:** prove the support version of `t:general` with
   `Continuous M`, together with whatever form of `c:gen` and
   `lem:frontier` best supports the main target.
7. **Independent optimization and main theorem:** independently derive and
   kernel-check sufficient parameter/slack inequalities, establish the uniform
   binomial estimate, and assemble the exact statement of `t:main`.

Each milestone ends with focused file checks and `lake build`, with no `sorry`,
`admit`, or new axioms.

## Scope decisions and remaining proof obligations

### Resolved decisions

- **G1 — outline prose:** irrelevant to the formalization. The literal
  `INCOMPLETE` at `paper/main.tex:330` belongs only to the informal outline;
  it does not qualify or block the detailed proof that follows.
- **G2 — `p>μ₀`:** remove this unnecessary hypothesis from the formal
  `t:bookmain`. Generalize `l:limit` to arbitrary `0<p<1`, `0<μ<1`, and
  derive `exists_bookExponent`: since `p^(1/r) → 1 > μ`, a natural `r≥2`
  eventually satisfies both `p^(1/r)>μ` and the strict inequality needed by
  the moment induction. The declaration docstring must note that the formal
  lemma strengthens the printed one.
- **G3 — regularity of `M`:** add `Continuous M` to the formal
  `t:general`. This deliberately narrows the abstract theorem and supplies the
  compact-interval uniformity used in its proof. The concrete applications must
  prove continuity of their chosen `M`.
- **G4 — generalized choose:** `chooseReal` is the root-level Mathlib
  `descPochhammer` evaluation divided by `b!`. The product formula,
  natural-input agreement, positivity, and Jensen interface are implemented.
  Instead of the printed exponential form of `f:binomial`, the development
  proves `chooseReal_lower_bound_four_fifths` under `5b² ≤ σm`, precisely the
  stronger regime available in `l:BBook`. Its `4/5` factor combines with the
  two later `4/5` losses to give `64/125 > 1/2`, so it is sufficient for the
  paper's blue-book conclusion.
- **G6:** all of `r:final` is excluded, so neither its endpoint nor its
  unverified AI-generated improvement is a proof obligation.
- **G7/G8:** the Multicolor section is excluded in full; its typos and omitted
  steps are not proof obligations.

### Active obligations

- **G5 — independent optimization:** do not translate the Mathematica-based
  `lem:numerics` certificate mechanically. Redo the optimization for the Lean
  development and kernel-check sufficient analytic or interval inequalities.
  The result must recover the exact coefficient function in `t:main`, or first
  prove a pointwise stronger exponent and then derive the printed bound. The
  paper's particular intermediate margins are not targets.
- **G9 — uniform asymptotics and Stirling:** formalize
  `R(k,ℓ)=e^{o(k)}` in the regime `ℓ=o(k)`, the two-variable error used for
  `o:r(4)`, and the binomial/Stirling estimate uniformly for every
  `1≤ℓ≤k`. Pointwise asymptotics are insufficient.
- **G10 — boundaries and rounding:** fix behavior for `k=0`, `ℓ=0`, empty
  finsets, closure boundary coordinates, real thresholds versus integer graph
  orders, floors/ceilings, and the minimum Ramsey number. The two public target
  statements carry positive-parameter hypotheses; density remains zero on
  empty inputs.

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
  rational inequalities can discharge algebraic leaves. The transcendental
  part of the independently reconstructed optimization in G5 will additionally
  need proved analytic bounds or a kernel-checked interval method.

Re-run a focused `#check`/`#find` audit in each module before fixing imports;
this inventory records available interfaces, not a promise that every needed
bridge lemma already exists.
