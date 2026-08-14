import Mathlib.Analysis.SpecialFunctions.Pochhammer
import Mathlib.Tactic

/-!
# Generalized real binomial coefficients

The paper uses `binom(x,b)` with a real upper argument.  We interpret it as
the descending Pochhammer polynomial evaluated at `x`, divided by `b!`.
This module records the product, natural-input, positivity, Jensen, and
quantitative lower-bound interfaces needed by the blue-book extraction.
-/

set_option autoImplicit false

namespace RamseyLean

open scoped Finset

/-- The generalized binomial coefficient `binom(x,b)` for a real upper
argument, defined by the descending Pochhammer polynomial. -/
noncomputable def chooseReal (x : ℝ) (b : ℕ) : ℝ :=
  (descPochhammer ℝ b).eval x / b.factorial

@[simp]
theorem chooseReal_zero (x : ℝ) : chooseReal x 0 = 1 := by
  simp [chooseReal]

theorem chooseReal_eq_prod_range (x : ℝ) (b : ℕ) :
    chooseReal x b =
      (∏ i ∈ Finset.range b, (x - (i : ℝ))) / b.factorial := by
  rw [chooseReal, descPochhammer_eval_eq_prod_range]

/-- On natural upper arguments, `chooseReal` agrees with `Nat.choose`. -/
@[simp]
theorem chooseReal_natCast (m b : ℕ) :
    chooseReal (m : ℝ) b = (m.choose b : ℝ) := by
  rw [chooseReal, ← Nat.cast_choose_eq_descPochhammer_div]

theorem chooseReal_nonneg {x : ℝ} {b : ℕ} (h : (b - 1 : ℝ) ≤ x) :
    0 ≤ chooseReal x b := by
  unfold chooseReal
  exact div_nonneg (descPochhammer_nonneg h) (by positivity)

theorem chooseReal_pos {x : ℝ} {b : ℕ} (h : (b - 1 : ℝ) < x) :
    0 < chooseReal x b := by
  unfold chooseReal
  exact div_pos (descPochhammer_pos h) (by positivity)

/-- Jensen's inequality for `chooseReal`, specialized to a finite weighted
average of natural upper arguments. -/
theorem chooseReal_le_weighted_sum
    {b : ℕ} (hb : b ≠ 0) {ι : Type*} {s : Finset ι}
    (p : ι → ℕ) (w : ι → ℝ)
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1)
    (havg : (b - 1 : ℝ) ≤ ∑ i ∈ s, w i * p i) :
    chooseReal (∑ i ∈ s, w i * p i) b ≤
      ∑ i ∈ s, w i * (p i).choose b := by
  exact descPochhammer_eval_div_factorial_le_sum_choose
    hb p w hw₀ hw₁ havg

private theorem one_sub_sum_le_prod_one_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (h₀ : ∀ i ∈ s, 0 ≤ f i) (h₁ : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      calc
        1 - (f a + ∑ i ∈ s, f i) ≤
            (1 - f a) * (1 - ∑ i ∈ s, f i) := by
          have hfa := h₀ a (Finset.mem_insert_self a s)
          have hsum : 0 ≤ ∑ i ∈ s, f i :=
            Finset.sum_nonneg fun i hi => h₀ i (Finset.mem_insert_of_mem hi)
          nlinarith
        _ ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) := by
          gcongr
          · exact sub_nonneg.mpr (h₁ a (Finset.mem_insert_self a s))
          · exact ih (fun i hi => h₀ i (Finset.mem_insert_of_mem hi))
              (fun i hi => h₁ i (Finset.mem_insert_of_mem hi))

private theorem two_mul_sum_range_cast_le_sq (b : ℕ) :
    2 * ∑ i ∈ Finset.range b, (i : ℝ) ≤ (b : ℝ) ^ 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.sum_range_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg (b : ℝ)]

/-- Direct replacement for paper Fact `f:binomial`, specialized to the
stronger regime used by `l:BBook`.  The paper proves an exponential factor
under `b ≤ σm/2`; downstream it has `5b² ≤ σm`, where the elementary product
estimate below gives the sufficient factor `4/5` without logarithms. -/
theorem chooseReal_lower_bound_four_fifths {σ : ℝ} {b m : ℕ}
    (hσ : 0 < σ) (_hσ₁ : σ ≤ 1) (hb : 0 < b) (hm : 0 < m)
    (hsq : 5 * (b : ℝ) ^ 2 ≤ σ * (m : ℝ)) :
    (4 / 5 : ℝ) * σ ^ b * (m.choose b : ℝ) ≤
      chooseReal (σ * (m : ℝ)) b := by
  let x : ℝ := σ * (m : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hb_one : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_le_x : (b : ℝ) ≤ x := by
    dsimp [x]
    nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hi_nonneg : ∀ i ∈ Finset.range b, 0 ≤ (i : ℝ) / x := by
    intro i hi
    positivity
  have hi_le_one : ∀ i ∈ Finset.range b, (i : ℝ) / x ≤ 1 := by
    intro i hi
    rw [div_le_one hx]
    exact (Nat.cast_lt.2 (Finset.mem_range.1 hi)).le.trans hb_le_x
  have hsum : (∑ i ∈ Finset.range b, (i : ℝ) / x) ≤ 1 / 5 := by
    rw [← Finset.sum_div, div_le_iff₀ hx]
    have htwo := two_mul_sum_range_cast_le_sq b
    dsimp [x] at hx ⊢
    nlinarith
  have hprod_four_fifths :
      (4 / 5 : ℝ) ≤ ∏ i ∈ Finset.range b, (1 - (i : ℝ) / x) := by
    calc
      (4 / 5 : ℝ) ≤ 1 - ∑ i ∈ Finset.range b, (i : ℝ) / x := by
        linarith
      _ ≤ ∏ i ∈ Finset.range b, (1 - (i : ℝ) / x) :=
        one_sub_sum_le_prod_one_sub _ _ hi_nonneg hi_le_one
  have hprod_identity :
      (∏ i ∈ Finset.range b, (x - (i : ℝ))) =
        x ^ b * ∏ i ∈ Finset.range b, (1 - (i : ℝ) / x) := by
    calc
      (∏ i ∈ Finset.range b, (x - (i : ℝ))) =
          ∏ i ∈ Finset.range b, (x * (1 - (i : ℝ) / x)) := by
        apply Finset.prod_congr rfl
        intro i hi
        field_simp
      _ = x ^ b * ∏ i ∈ Finset.range b, (1 - (i : ℝ) / x) := by
        rw [Finset.prod_mul_distrib]
        simp
  have hdesc : (m.descFactorial b : ℝ) ≤ (m : ℝ) ^ b := by
    exact_mod_cast Nat.descFactorial_le_pow m b
  have hraw :
      (4 / 5 : ℝ) * σ ^ b * (m.descFactorial b : ℝ) ≤
        ∏ i ∈ Finset.range b, (x - (i : ℝ)) := by
    rw [hprod_identity]
    have hxpow : x ^ b = σ ^ b * (m : ℝ) ^ b := by
      simp [x, mul_pow]
    rw [hxpow]
    calc
      (4 / 5 : ℝ) * σ ^ b * (m.descFactorial b : ℝ) ≤
          (4 / 5 : ℝ) * σ ^ b * (m : ℝ) ^ b := by gcongr
      _ = (σ ^ b * (m : ℝ) ^ b) * (4 / 5 : ℝ) := by ring
      _ ≤ (σ ^ b * (m : ℝ) ^ b) *
          (∏ i ∈ Finset.range b, (1 - (i : ℝ) / x)) := by gcongr
  rw [chooseReal, descPochhammer_eval_eq_prod_range]
  have hfac : (0 : ℝ) < b.factorial := by positivity
  rw [Nat.cast_choose_eq_descPochhammer_div (K := ℝ) m b,
    descPochhammer_eval_eq_descFactorial]
  calc
    (4 / 5 : ℝ) * σ ^ b *
          ((m.descFactorial b : ℝ) / b.factorial) =
        ((4 / 5 : ℝ) * σ ^ b * (m.descFactorial b : ℝ)) /
          b.factorial := by ring
    _ ≤ (∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ))) /
          b.factorial := (div_le_div_iff_of_pos_right hfac).2 (by simpa [x] using hraw)

end RamseyLean
