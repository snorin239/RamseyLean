# Optimizing the CGMS upper bound on Ramsey numbers in Lean

This repository contains a Lean 4 + Mathlib formalization of Theorem 1 and
Corollary 6 of Parth Gupta, Ndiamé Ndiaye, Sergey Norin, and Louis Wei,
[*Optimizing the CGMS upper bound on Ramsey
numbers*](paper/main.pdf). An earlier version is available as
[arXiv:2407.19026](https://arxiv.org/abs/2407.19026). The bundled PDF is the
latest version and is the source for all statement wording and numbering
below.

## The statements being formalized

The Ramsey number `R(k, ℓ)` is the least `N` such that every red-blue coloring
of the complete graph on `N` vertices contains either a red `K_k` or a blue
`K_ℓ`. The development represents a coloring by its red graph, with blue edges
given by the complement:

```lean
def RamseyBound (k ℓ N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    hasRedClique G Finset.univ k ∨ hasBlueClique G Finset.univ ℓ

noncomputable def ramseyNumber (k ℓ : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_ramseyBound k ℓ)

def ramseyLinearScale (k : ℕ) : ℝ := k

def SublinearError (η : ℕ → ℝ) : Prop :=
  η =o[atTop] ramseyLinearScale
```

Thus `SublinearError η` says that `η(k) = o(k)` as `k → ∞`.

### Theorem 1

For all positive integers `ℓ ≤ k`,

$$
R(k,\ell) \leq
\exp\!\left(G(\ell/k)k+o(k)\right)\binom{k+\ell}{\ell},
\qquad
G(\lambda)=\left(-\frac14\lambda+\frac{3}{100}\lambda^2
+\frac{2}{25}\lambda^3\right)e^{-\lambda}.
$$

The Lean theorem makes the uniform meaning of `o(k)` explicit: a single error
function `η`, independent of `ℓ`, works simultaneously for every positive
`ℓ ≤ k`.

```lean
theorem main :
    ∃ η : ℕ → ℝ,
      SublinearError η ∧
      ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
        (ramseyNumber k ℓ : ℝ) ≤
          Real.exp
              (((-(1 / 4 : ℝ) * ((ℓ : ℝ) / (k : ℝ)) +
                    (3 / 100 : ℝ) * ((ℓ : ℝ) / (k : ℝ)) ^ 2 +
                    (2 / 25 : ℝ) * ((ℓ : ℝ) / (k : ℝ)) ^ 3) *
                  Real.exp (-((ℓ : ℝ) / (k : ℝ)))) *
                (k : ℝ) + η k) *
            (Nat.choose (k + ℓ) ℓ : ℝ)
```

The decimal coefficients in the paper are represented by the exact rational
numbers `1/4`, `3/100`, and `2/25`.

### Corollary 6

For all positive integers `ℓ ≤ k`,

$$
R(k,\ell) \leq
4(k+\ell)
\left(\frac{(\sqrt5+1)(k+2\ell)}{4\ell}\right)^\ell
\left(\frac{k+2\ell}{k}\right)^{k/2}.
$$

Its printed statement is exposed directly as follows:

```lean
theorem ramseyNumber_le_easy_optimized {k ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    (ramseyNumber k ℓ : ℝ) ≤
      4 * ((k : ℝ) + (ℓ : ℝ)) *
        (((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ))) /
          (4 * (ℓ : ℝ))) ^ ℓ *
        (((k : ℝ) + 2 * (ℓ : ℝ)) / (k : ℝ)) ^ ((k : ℝ) / 2)
```

The power indexed by `ℓ` is a natural power. The final power is `Real.rpow`,
as required by the real exponent `k/2`, including when `k` is odd.

## Structure of the proof

1. **Finite graph foundations.** Ramsey bounds are defined using a graph and
   its complement, and the usual recurrence and finite counting identities
   are proved.
2. **The elementary excess argument.** Candidate and excess inequalities are
   combined with a deterministic weighted bipartition argument to prove
   Corollary 6.
3. **Book induction.** Generalized binomial estimates, blue-book extraction,
   degree regularization, and uniform asymptotic bounds provide the main
   book-induction result.
4. **Descent and the frontier.** Dense and sparse cases are assembled into a
   uniform descent theorem, and a concave frontier construction feeds stronger
   Ramsey bounds into a second descent.
5. **Certified numerical optimization.** Independently selected parameters and
   kernel-checked interval certificates establish the exponential correction
   in Theorem 1.
6. **Final assembly.** A uniform one-sided Stirling estimate converts the
   exponential entropy bound into the binomial form stated in Theorem 1.

The revised manuscript and the Lean development agree on the relevant
parameter conditions: Lemma 11 assumes `0 < p` and `μ < 1`, while Lemma 12
assumes `0 < μ₀, x₀, y₀, p < 1` and has no extra `p > μ₀` hypothesis. Other
intermediate results are sometimes strengthened, generalized, or replaced by
sufficient statements better suited to Lean; see
[`FORMALIZATION.md`](FORMALIZATION.md) for the paper-to-Lean map.

## Certified numerical optimization

The numerical optimization was redone independently for this formalization.
The manuscript's Mathematica-assisted certificate is not imported as proof
evidence. Instead, the development proves soundness theorems for fixed-point
interval arithmetic, Taylor enclosures, and outward rounding. Certificate
endpoints and checker decisions are exact integers; floating-point sampling
was used only to choose parameters and meshes. Every inequality used to reach
Theorem 1 is ultimately checked by Lean's kernel.

## Scope

The repository formalizes Theorem 1 and Corollary 6 together with the results
needed for their proofs. Remark 17, including its preliminary unverified
further optimization, and Section 5 (Observation 18 through Remark 22) are
intentionally outside scope.

## Building

The project pins Lean and Mathlib to `v4.32.1`. After installing
[Elan](https://lean-lang.org/install/) and Git, run from the repository root:

```text
lake exe cache get
lake build
```

The root target checks the complete formalization, including the concrete
numerical certificates. No external numerical program or untrusted generated
output is needed during the build.

## Verification

The full `lake build` succeeds. The Lean source contains no `sorry`, `admit`,
or user-declared placeholder axioms. For both `RamseyLean.main` and
`RamseyLean.ramseyNumber_le_easy_optimized`, `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Attribution

This formalization, including its documentation, was produced by OpenAI Codex
(GPT-5.6 Sol, Ultra reasoning), with minimal guidance from the paper's authors.
