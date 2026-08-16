import RamseyLean.Numerics
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Main Ramsey bound

This module completes paper Theorem `t:main`.  A global form of Stirling's
formula supplies the final binomial-entropy comparison uniformly for every
`1 ≤ ℓ ≤ k`; its explicit logarithmic error is then combined with the uniform
error produced by the certified numerical descent.
-/

set_option autoImplicit false

namespace RamseyLean

open Filter Asymptotics

noncomputable section

private theorem log_factorial_le_stirling_upper {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hmono :
      Real.log (Stirling.stirlingSeq (m + 1)) ≤
        Real.log (Stirling.stirlingSeq 1) := by
    exact Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  have hconst :
      Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one,
      Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt (by positivity)]
  rw [Stirling.log_stirlingSeq_formula, hconst,
    Real.log_div (by positivity) (by positivity), Real.log_exp] at hmono
  rw [Real.log_mul (by norm_num) (by positivity)] at hmono
  nlinarith

private theorem log_choose_add (k ℓ : ℕ) :
    Real.log (Nat.choose (k + ℓ) ℓ : ℝ) =
      Real.log ((k + ℓ).factorial : ℝ) -
        Real.log (k.factorial : ℝ) - Real.log (ℓ.factorial : ℝ) := by
  have hℓsum : ℓ ≤ k + ℓ := by omega
  have hnat :
      Nat.choose (k + ℓ) ℓ * ℓ.factorial * k.factorial =
        (k + ℓ).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial hℓsum
  have hcast :
      (Nat.choose (k + ℓ) ℓ : ℝ) * (ℓ.factorial : ℝ) * (k.factorial : ℝ) =
        ((k + ℓ).factorial : ℝ) := by
    exact_mod_cast hnat
  have hchoose0 : (Nat.choose (k + ℓ) ℓ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hℓsum))
  have hℓfac0 : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have hkfac0 : (k.factorial : ℝ) ≠ 0 := by positivity
  have hlog := congrArg Real.log hcast
  rw [Real.log_mul (mul_ne_zero hchoose0 hℓfac0) hkfac0,
    Real.log_mul hchoose0 hℓfac0] at hlog
  linarith

private theorem entropy_ratio_mul {k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) =
      ((k + ℓ : ℕ) : ℝ) * Real.log (k + ℓ) -
        (k : ℝ) * Real.log k - (ℓ : ℝ) * Real.log ℓ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsumR : (0 : ℝ) < k + ℓ := by positivity
  have hone :
      1 + (ℓ : ℝ) / (k : ℝ) = ((k + ℓ : ℕ) : ℝ) / (k : ℝ) := by
    rw [Nat.cast_add]
    field_simp [hkR.ne']
  rw [entropy, hone]
  push_cast
  rw [Real.log_div hsumR.ne' hkR.ne', Real.log_div hℓR.ne' hkR.ne']
  field_simp [hkR.ne']
  ring

/-- The explicit `O(log k)` loss in the uniform binomial-entropy estimate. -/
def binomialEntropyError (k : ℕ) : ℝ :=
  Real.log (k : ℝ) / 2 + 2

theorem sublinearError_binomialEntropyError :
    SublinearError binomialEntropyError := by
  have hlog : SublinearError (fun k : ℕ => Real.log (k : ℝ)) := by
    change (fun k : ℕ => Real.log (k : ℝ)) =o[atTop]
      (fun k : ℕ => (k : ℝ))
    exact Real.isLittleO_log_id_atTop.natCast_atTop
  change (fun k : ℕ => Real.log (k : ℝ) / 2 + 2) =o[atTop]
    ramseyLinearScale
  simpa [binomialEntropyError, div_eq_mul_inv, mul_comm] using
    (hlog.const_mul_left (2 : ℝ)⁻¹).add (sublinearError_const 2)

private theorem entropy_mul_le_log_choose_add_error {k ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) ≤
      Real.log (Nat.choose (k + ℓ) ℓ : ℝ) + binomialEntropyError k := by
  have hk : 0 < k := lt_of_lt_of_le hℓ hℓk
  have hsum0 : k + ℓ ≠ 0 := by omega
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  have hsumLower := Stirling.le_log_factorial_stirling hsum0
  have hkUpper := log_factorial_le_stirling_upper hk0
  have hℓUpper := log_factorial_le_stirling_upper hℓ0
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓsumR : (ℓ : ℝ) ≤ (k + ℓ : ℕ) := by
    exact_mod_cast (show ℓ ≤ k + ℓ by omega)
  have hlogℓsum : Real.log (ℓ : ℝ) ≤ Real.log (k + ℓ : ℕ) :=
    Real.log_le_log hℓR hℓsumR
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  push_cast at hsumLower hlogℓsum
  rw [log_choose_add, entropy_ratio_mul hk hℓ]
  dsimp [binomialEntropyError]
  push_cast
  linarith

private theorem choose_entropy_lower_bound {k ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    Real.exp
        (entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) - binomialEntropyError k) ≤
      (Nat.choose (k + ℓ) ℓ : ℝ) := by
  have hchoosePos : 0 < (Nat.choose (k + ℓ) ℓ : ℝ) := by
    exact_mod_cast Nat.choose_pos (show ℓ ≤ k + ℓ by omega)
  rw [← Real.exp_log hchoosePos]
  apply Real.exp_le_exp.mpr
  linarith [entropy_mul_le_log_choose_add_error hℓ hℓk]

/-- The one-sided uniform binomial/Stirling estimate used in the final step of
paper Theorem `t:main`.  This is a sufficient replacement for the manuscript's
stronger two-sided display
`log ((k + ℓ).choose ℓ) = entropy (ℓ / k) * k + o(k)`: only its lower side is
needed to absorb the entropy term into the binomial coefficient. -/
theorem uniform_choose_entropy_lower_bound :
    ∃ ξ : ℕ → ℝ,
      SublinearError ξ ∧
      ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
        Real.exp
            (entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) - ξ k) ≤
          (Nat.choose (k + ℓ) ℓ : ℝ) := by
  exact ⟨binomialEntropyError, sublinearError_binomialEntropyError,
    fun k ℓ hℓ hℓk => choose_entropy_lower_bound hℓ hℓk⟩

/-- Uniform assembly form of paper Theorem `t:main`. -/
theorem main_uniform :
    ∃ η : ℕ → ℝ,
      SublinearError η ∧
      ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
        (ramseyNumber k ℓ : ℝ) ≤
          Real.exp
              (g finalB ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + η k) *
            (Nat.choose (k + ℓ) ℓ : ℝ) := by
  rcases uniformRamseyExpBound_final with ⟨w⟩
  rcases uniform_choose_entropy_lower_bound with ⟨ξ, hξ, hchoose⟩
  refine ⟨fun k => w.error k + ξ k, w.error_sublinear.add hξ, ?_⟩
  intro k ℓ hℓ hℓk
  let r : ℝ := (ℓ : ℝ) / (k : ℝ)
  calc
    (ramseyNumber k ℓ : ℝ) ≤
        Real.exp (F finalB r * (k : ℝ) + w.error k) :=
      w.bound k ℓ hℓ hℓk
    _ = Real.exp
          (g finalB r * (k : ℝ) + (w.error k + ξ k)) *
        Real.exp (entropy r * (k : ℝ) - ξ k) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [F]
      ring
    _ ≤ Real.exp
          (g finalB r * (k : ℝ) + (w.error k + ξ k)) *
        (Nat.choose (k + ℓ) ℓ : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (hchoose k ℓ hℓ hℓk) (Real.exp_pos _).le

/-- Paper Theorem `t:main`, with its printed statement unchanged apart from
explicit casts and one error function expressing the uniform `o(k)` term. -/
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
            (Nat.choose (k + ℓ) ℓ : ℝ) := by
  simpa [g, gPoly, finalB] using main_uniform

end


end RamseyLean
