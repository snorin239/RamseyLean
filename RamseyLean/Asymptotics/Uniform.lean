import RamseyLean.Ramsey
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Explicit uniform asymptotic Ramsey bounds

This module formalizes the uniform interpretation of the paper's `o(k)`
notation used in `t:general` and `t:main`.  An error term depends only on the
larger clique parameter `k`, so the same witness applies simultaneously to
every `1 ≤ ℓ ≤ k`.

The primary interface is a direct real bound on `ramseyNumber`, which avoids
rounding losses in asymptotic arguments.  A natural-ceiling bridge exposes the
corresponding `RamseyBound` whenever a finite graph theorem needs it.
-/

set_option autoImplicit false

namespace RamseyLean

open Filter Asymptotics

/-- The linear scale against which all one-parameter error terms are measured. -/
def ramseyLinearScale (k : ℕ) : ℝ := k

/-- An explicit error term which is `o(k)` as `k → ∞`. -/
def SublinearError (η : ℕ → ℝ) : Prop :=
  η =o[atTop] ramseyLinearScale

/-- A witness for a Ramsey bound of the form
`R(k,ℓ) ≤ exp (F(ℓ/k) k + o(k))`, uniformly for `1 ≤ ℓ ≤ k`.

Keeping the error function as data makes the uniformity in `ℓ` explicit and
lets later proofs compose error terms without unpacking nested existentials. -/
structure UniformRamseyExpWitness (F : ℝ → ℝ) where
  error : ℕ → ℝ
  error_sublinear : SublinearError error
  bound : ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
    (ramseyNumber k ℓ : ℝ) ≤
      Real.exp (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + error k)

/-- The existential uniform exponential Ramsey-bound predicate. -/
def UniformRamseyExpBound (F : ℝ → ℝ) : Prop :=
  Nonempty (UniformRamseyExpWitness F)

/-- Epsilon/eventual formulation of the same uniform exponential bound. -/
def EventuallyUniformRamseyExpBound (F : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k in atTop, ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
      (ramseyNumber k ℓ : ℝ) ≤
        Real.exp ((F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ))

/-- The canonical error is the largest positive logarithmic deficit among all
`1 ≤ ℓ ≤ k`.  The range also contains `ℓ = 0`, assigned deficit zero, so the
finite supremum is always defined and nonnegative, including at `k = 0`. -/
noncomputable def uniformRamseyLogError (F : ℝ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sup' (by simp) fun ℓ =>
    if 0 < ℓ then
      max 0
        (Real.log (ramseyNumber k ℓ : ℝ) -
          F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ))
    else 0

theorem uniformRamseyLogError_nonneg (F : ℝ → ℝ) (k : ℕ) :
    0 ≤ uniformRamseyLogError F k := by
  unfold uniformRamseyLogError
  have hzero : 0 ∈ Finset.range (k + 1) := by simp
  have h := Finset.le_sup'
    (s := Finset.range (k + 1))
    (f := fun ℓ =>
      if 0 < ℓ then
        max 0
          (Real.log (ramseyNumber k ℓ : ℝ) -
            F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ))
      else 0)
    hzero
  simpa using h

theorem log_deficit_le_uniformRamseyLogError (F : ℝ → ℝ)
    {k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    Real.log (ramseyNumber k ℓ : ℝ) -
        F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) ≤
      uniformRamseyLogError F k := by
  unfold uniformRamseyLogError
  have hmem : ℓ ∈ Finset.range (k + 1) := by
    simp only [Finset.mem_range]
    omega
  exact (le_max_right 0 _).trans (by
    simpa [hℓ] using
      (Finset.le_sup'
        (s := Finset.range (k + 1))
        (f := fun j =>
          if 0 < j then
            max 0
              (Real.log (ramseyNumber k j : ℝ) -
                F ((j : ℝ) / (k : ℝ)) * (k : ℝ))
          else 0)
        hmem))

/-- The canonical logarithmic error gives an exact bound for every admissible
pair, independently of any asymptotic hypothesis. -/
theorem ramseyNumber_le_exp_uniformRamseyLogError (F : ℝ → ℝ)
    {k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    (ramseyNumber k ℓ : ℝ) ≤
      Real.exp
        (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + uniformRamseyLogError F k) := by
  apply Real.le_exp_of_log_le
  linarith [log_deficit_le_uniformRamseyLogError F hℓ hℓk]

@[simp]
theorem sublinearError_zero : SublinearError (fun _ : ℕ => (0 : ℝ)) := by
  exact isLittleO_zero ramseyLinearScale atTop

theorem sublinearError_const (c : ℝ) :
    SublinearError (fun _ : ℕ => c) := by
  change (fun _ : ℕ => c) =o[atTop] (fun k : ℕ => (k : ℝ))
  exact (isLittleO_const_id_atTop c).natCast_atTop

theorem SublinearError.add {η θ : ℕ → ℝ}
    (hη : SublinearError η) (hθ : SublinearError θ) :
    SublinearError (fun k => η k + θ k) := by
  exact Asymptotics.IsLittleO.add hη hθ

theorem SublinearError.abs {η : ℕ → ℝ} (hη : SublinearError η) :
    SublinearError (fun k => |η k|) := by
  exact hη.abs_left

theorem SublinearError.congr' {η θ : ℕ → ℝ} (hη : SublinearError η)
    (hηθ : η =ᶠ[atTop] θ) : SublinearError θ := by
  exact Asymptotics.IsLittleO.congr' hη hηθ EventuallyEq.rfl

/-- Epsilon/eventual form of an explicit sublinear error. -/
theorem SublinearError.eventually_abs_le {η : ℕ → ℝ}
    (hη : SublinearError η) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, |η k| ≤ ε * (k : ℝ) := by
  simpa [ramseyLinearScale, Real.norm_eq_abs, abs_of_nonneg] using hη.def hε

/-- The canonical logarithmic deficit is sublinear whenever every positive
epsilon eventually works uniformly in `ℓ`. -/
theorem sublinearError_uniformRamseyLogError {F : ℝ → ℝ}
    (hF : EventuallyUniformRamseyExpBound F) :
    SublinearError (uniformRamseyLogError F) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hF ε hε, eventually_gt_atTop 0] with k hbound hk
  have herror : uniformRamseyLogError F k ≤ ε * (k : ℝ) := by
    unfold uniformRamseyLogError
    apply Finset.sup'_le
    intro ℓ hℓmem
    by_cases hℓ : 0 < ℓ
    · simp only [if_pos hℓ]
      have hℓk : ℓ ≤ k := by
        simp only [Finset.mem_range] at hℓmem
        omega
      have hRpos : 0 < (ramseyNumber k ℓ : ℝ) := by
        exact_mod_cast ramseyNumber_pos hk hℓ
      have hlog :
          Real.log (ramseyNumber k ℓ : ℝ) ≤
            (F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ) :=
        (Real.log_le_iff_le_exp hRpos).2 (hbound ℓ hℓ hℓk)
      rw [add_mul] at hlog
      exact max_le (mul_nonneg hε.le (by positivity)) (by linarith)
    · simp only [if_neg hℓ]
      exact mul_nonneg hε.le (by positivity)
  simpa [ramseyLinearScale, Real.norm_eq_abs,
    abs_of_nonneg (uniformRamseyLogError_nonneg F k),
    abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)] using herror

/-- Converse bridge: an epsilon/eventual bound produces one explicit error
function, uniform in every `1 ≤ ℓ ≤ k`. -/
theorem uniformRamseyExpBound_of_eventually {F : ℝ → ℝ}
    (hF : EventuallyUniformRamseyExpBound F) :
    UniformRamseyExpBound F := by
  exact ⟨{
    error := uniformRamseyLogError F
    error_sublinear := sublinearError_uniformRamseyLogError hF
    bound := fun _ _ hℓ hℓk =>
      ramseyNumber_le_exp_uniformRamseyLogError F hℓ hℓk }⟩

/-- An explicit uniform witness implies the epsilon/eventual formulation. -/
theorem UniformRamseyExpBound.eventually {F : ℝ → ℝ}
    (hF : UniformRamseyExpBound F) : EventuallyUniformRamseyExpBound F := by
  rcases hF with ⟨w⟩
  intro ε hε
  filter_upwards [w.error_sublinear.eventually_abs_le hε] with k hk
  intro ℓ hℓ hℓk
  refine (w.bound k ℓ hℓ hℓk).trans (Real.exp_le_exp.mpr ?_)
  rw [add_mul]
  exact add_le_add le_rfl ((le_abs_self (w.error k)).trans hk)

theorem uniformRamseyExpBound_iff_eventually {F : ℝ → ℝ} :
    UniformRamseyExpBound F ↔ EventuallyUniformRamseyExpBound F :=
  ⟨UniformRamseyExpBound.eventually, uniformRamseyExpBound_of_eventually⟩

/-- The existential predicate is definitionally equivalent to the explicit
error-function formulation used in the statement of the main theorem. -/
theorem uniformRamseyExpBound_iff {F : ℝ → ℝ} :
    UniformRamseyExpBound F ↔
      ∃ η : ℕ → ℝ,
        SublinearError η ∧
          ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
            (ramseyNumber k ℓ : ℝ) ≤
              Real.exp (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + η k) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.error, w.error_sublinear, w.bound⟩
  · rintro ⟨η, hη, hbound⟩
    exact ⟨⟨η, hη, hbound⟩⟩

/-- Simultaneously weaken the rate and replace the error term, provided the
resulting complete exponent is pointwise larger on every admissible pair. -/
def UniformRamseyExpWitness.weaken {F G : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) {θ : ℕ → ℝ}
    (hθ : SublinearError θ)
    (hexp : ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
      F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + w.error k ≤
        G ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + θ k) :
    UniformRamseyExpWitness G where
  error := θ
  error_sublinear := hθ
  bound := by
    intro k ℓ hℓ hℓk
    exact (w.bound k ℓ hℓ hℓk).trans
      (Real.exp_le_exp.mpr (hexp k ℓ hℓ hℓk))

/-- Pointwise enlargement of an error term preserves the bound.  The new
error must separately be proved sublinear. -/
def UniformRamseyExpWitness.weakenError {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) {θ : ℕ → ℝ}
    (hθ : SublinearError θ) (hηθ : ∀ k, w.error k ≤ θ k) :
    UniformRamseyExpWitness F :=
  w.weaken hθ (fun k _ _ _ => add_le_add le_rfl (hηθ k))

/-- Replace an arbitrary error witness by its nonnegative absolute value. -/
def UniformRamseyExpWitness.absError {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) : UniformRamseyExpWitness F :=
  w.weakenError w.error_sublinear.abs (fun k => le_abs_self (w.error k))

/-- Adding a nonnegative sublinear allowance to a witness is a convenient
composition operation for later analytic estimates. -/
def UniformRamseyExpWitness.addError {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) {θ : ℕ → ℝ}
    (hθ : SublinearError θ) (hθnonneg : ∀ k, 0 ≤ θ k) :
    UniformRamseyExpWitness F :=
  w.weakenError (w.error_sublinear.add hθ) (fun k => by
    simpa only [le_add_iff_nonneg_right] using hθnonneg k)

/-- Absorb a fixed nonnegative amount into the exponent. -/
def UniformRamseyExpWitness.addConst {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) (c : ℝ) (hc : 0 ≤ c) :
    UniformRamseyExpWitness F :=
  w.addError (sublinearError_const c) (fun _ => hc)

private theorem ratio_mem_Ioc {k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    (ℓ : ℝ) / (k : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
  have hk : 0 < k := lt_of_lt_of_le hℓ hℓk
  constructor
  · positivity
  · exact (div_le_one (by positivity)).2 (by exact_mod_cast hℓk)

/-- Weakening the exponential rate on `(0,1]` preserves a uniform bound. -/
def UniformRamseyExpWitness.weakenRate {F G : ℝ → ℝ}
    (w : UniformRamseyExpWitness F)
    (hFG : ∀ x ∈ Set.Ioc (0 : ℝ) 1, F x ≤ G x) :
    UniformRamseyExpWitness G where
  error := w.error
  error_sublinear := w.error_sublinear
  bound := by
    intro k ℓ hℓ hℓk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    exact (w.bound k ℓ hℓ hℓk).trans
      (Real.exp_le_exp.mpr
        (add_le_add (mul_le_mul_of_nonneg_right
          (hFG _ (ratio_mem_Ioc hℓ hℓk)) hk0) le_rfl))

theorem UniformRamseyExpBound.weakenRate {F G : ℝ → ℝ}
    (hF : UniformRamseyExpBound F)
    (hFG : ∀ x ∈ Set.Ioc (0 : ℝ) 1, F x ≤ G x) :
    UniformRamseyExpBound G := by
  rcases hF with ⟨w⟩
  exact ⟨w.weakenRate hFG⟩

/-- Symmetric specialization to the other half of the positive quadrant. -/
theorem UniformRamseyExpWitness.bound_of_ge {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) (k ℓ : ℕ) (hk : 0 < k) (hkℓ : k ≤ ℓ) :
    (ramseyNumber k ℓ : ℝ) ≤
      Real.exp (F ((k : ℝ) / (ℓ : ℝ)) * (ℓ : ℝ) + w.error ℓ) := by
  rw [ramseyNumber_comm]
  exact w.bound ℓ k hk hkℓ

/-- Symmetric all-positive-parameters form, using the larger clique parameter
as the uniform scale. -/
theorem UniformRamseyExpWitness.bound_max {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
    (ramseyNumber k ℓ : ℝ) ≤
      Real.exp
        (F (((min k ℓ : ℕ) : ℝ) / ((max k ℓ : ℕ) : ℝ)) *
            ((max k ℓ : ℕ) : ℝ) + w.error (max k ℓ)) := by
  rcases le_total ℓ k with hℓk | hkℓ
  · simpa [Nat.min_eq_right hℓk, Nat.max_eq_left hℓk] using
      w.bound k ℓ hℓ hℓk
  · simpa [Nat.min_eq_left hkℓ, Nat.max_eq_right hkℓ] using
      w.bound_of_ge k ℓ hk hkℓ

/-- Diagonal specialization of a uniform witness. -/
theorem UniformRamseyExpWitness.diagonal {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) (k : ℕ) (hk : 0 < k) :
    (ramseyNumber k k : ℝ) ≤
      Real.exp (F 1 * (k : ℝ) + w.error k) := by
  simpa [hk.ne'] using w.bound k k hk le_rfl

/-- Specialization along any sequence of admissible positive parameter pairs. -/
theorem UniformRamseyExpWitness.along {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) (k ℓ : ℕ → ℕ)
    (hℓ : ∀ n, 0 < ℓ n) (hℓk : ∀ n, ℓ n ≤ k n) (n : ℕ) :
    (ramseyNumber (k n) (ℓ n) : ℝ) ≤
      Real.exp
        (F (((ℓ n : ℕ) : ℝ) / ((k n : ℕ) : ℝ)) * ((k n : ℕ) : ℝ) +
          w.error (k n)) :=
  w.bound (k n) (ℓ n) (hℓ n) (hℓk n)

/-- Ramsey-predicate form obtained by rounding the real bound upward. -/
theorem UniformRamseyExpWitness.ramseyBound_ceiling {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) {k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    RamseyBound k ℓ
      ⌈Real.exp (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + w.error k)⌉₊ := by
  apply (ramseyNumber_spec k ℓ).mono
  have hreal :
      (ramseyNumber k ℓ : ℝ) ≤
        (⌈Real.exp (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + w.error k)⌉₊ : ℕ) :=
    (w.bound k ℓ hℓ hℓk).trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- The rounded witness supplies every larger graph order as a Ramsey bound. -/
theorem UniformRamseyExpWitness.ramseyBound_of_ceiling_le {F : ℝ → ℝ}
    (w : UniformRamseyExpWitness F) {k ℓ N : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k)
    (hN :
      ⌈Real.exp (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + w.error k)⌉₊ ≤ N) :
    RamseyBound k ℓ N :=
  (w.ramseyBound_ceiling hℓ hℓk).mono hN

/-- A literal bound without an error term yields a uniform asymptotic bound. -/
theorem uniformRamseyExpBound_of_exact {F : ℝ → ℝ}
    (h : ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
      (ramseyNumber k ℓ : ℝ) ≤
        Real.exp (F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ))) :
    UniformRamseyExpBound F := by
  refine ⟨{
    error := fun _ => 0
    error_sublinear := sublinearError_zero
    bound := ?_ }⟩
  intro k ℓ hℓ hℓk
  simpa using h k ℓ hℓ hℓk

end RamseyLean
