import RamseyLean.Numerics.Core

/-!
# Smooth form of the preliminary numerical slack

The independently retuned preliminary parameters are `b₀ = 3 / 40` and
`M₀(r) = r * exp (-(9 / 10) r - (1 / 20) r²)`.  Directly evaluating the
associated slack near `r = 0` creates several removable `0 / 0` expressions.
This module factors those expressions into smooth logarithmic and exponential
quotients and proves that the resulting normalized expression is exactly the
original slack divided by `r` on `0 < r ≤ 1`.
-/

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

/-- The polynomial remainder in the factored preliminary slope. -/
def preliminaryRemainder (r : ℝ) : ℝ :=
  -(1 / 4 : ℝ) + (2 / 5 : ℝ) * r + (33 / 200 : ℝ) * r ^ 2 -
    (2 / 25 : ℝ) * r ^ 3

/-- The quantity `exp (-F'_{b₀}(r))`, written with its factor `r` exposed. -/
def preliminaryA (r : ℝ) : ℝ :=
  r / (1 + r) * Real.exp (-Real.exp (-r) * preliminaryRemainder r)

/-- The `X` parameter in the preliminary descent. -/
def preliminaryX (r : ℝ) : ℝ :=
  numericalX preliminaryB preliminaryM r

/-- The complementary Erdős--Szekeres parameter in the preliminary descent. -/
def preliminaryY (r : ℝ) : ℝ :=
  1 - preliminaryX r

/-- The positive form of the preliminary descent slack. -/
def preliminarySlack (r : ℝ) : ℝ :=
  F preliminaryB r +
    (Real.log (preliminaryX r) + r * Real.log (preliminaryM r) +
      r * Real.log (preliminaryY r)) / 2

/-- The smooth quotient `-log (1-x) / x`, used only at positive `x`. -/
def preliminaryNegLogOneSubRatio (x : ℝ) : ℝ :=
  -Real.log (1 - x) / x

/-- The smooth quotient `(1-exp(-x))/x`, used only at positive `x`. -/
def preliminaryOneSubExpNegRatio (x : ℝ) : ℝ :=
  (1 - Real.exp (-x)) / x

/-- The factor `M₀(r) / r`, extended smoothly to `r = 0`. -/
def preliminaryMRatio (r : ℝ) : ℝ :=
  Real.exp (-(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2)

/-- The factor `exp (-F'_{b₀}(r)) / r`, extended smoothly to `r = 0`. -/
def preliminaryARatio (r : ℝ) : ℝ :=
  Real.exp (-Real.exp (-r) * preliminaryRemainder r) / (1 + r)

/-- The smooth factor `-log X₀(r) / r`. -/
def preliminaryU (r : ℝ) : ℝ :=
  preliminaryMRatio r * preliminaryNegLogOneSubRatio (preliminaryM r) +
    preliminaryARatio r * preliminaryNegLogOneSubRatio (preliminaryA r) /
      (1 - preliminaryM r)

/-- The smooth factor `(1-X₀(r)) / r`. -/
def preliminaryZ (r : ℝ) : ℝ :=
  preliminaryU r * preliminaryOneSubExpNegRatio (r * preliminaryU r)

/-- The preliminary slack divided by `r`, in a form with every removable
singularity exposed through a smooth quotient. -/
def preliminaryNormalizedSlack (r : ℝ) : ℝ :=
  (1 + r) * (Real.log (1 + r) / r) +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 40 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    preliminaryU r / 2 - (9 / 20 : ℝ) * r -
    (1 / 40 : ℝ) * r ^ 2 + Real.log (preliminaryZ r) / 2

theorem exp_neg_FSlope_preliminary {r : ℝ} (hr : 0 < r) :
    Real.exp (-FSlope preliminaryB r) = preliminaryA r := by
  have h1r : 0 < 1 + r := by linarith
  have hexponent :
      -FSlope preliminaryB r =
        (Real.log r - Real.log (1 + r)) +
          (-Real.exp (-r) * preliminaryRemainder r) := by
    simp only [FSlope, preliminaryB, preliminaryRemainder]
    ring
  rw [hexponent, Real.exp_add, Real.exp_sub, Real.exp_log hr,
    Real.exp_log h1r]
  rfl

theorem numericalP_preliminary_eq {r : ℝ} (hr : 0 < r) :
    numericalP preliminaryB r = 1 - preliminaryA r := by
  rw [numericalP, exp_neg_FSlope_preliminary hr]

theorem preliminaryM_eq_mul_ratio (r : ℝ) :
    preliminaryM r = r * preliminaryMRatio r := rfl

theorem preliminaryA_eq_mul_ratio {r : ℝ} (hr : 0 < r) :
    preliminaryA r = r * preliminaryARatio r := by
  dsimp [preliminaryA, preliminaryARatio]
  field_simp [hr.ne', (by linarith : 1 + r ≠ 0)]

theorem log_preliminaryX {r : ℝ}
    (hM : preliminaryM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP preliminaryB r ∈ Ioo (0 : ℝ) 1) :
    Real.log (preliminaryX r) = Real.log (1 - preliminaryM r) +
      Real.log (numericalP preliminaryB r) / (1 - preliminaryM r) := by
  have hOneM : 0 < 1 - preliminaryM r := sub_pos.mpr hM.2
  have hpow : 0 < Real.rpow (numericalP preliminaryB r)
      (1 / (1 - preliminaryM r)) := Real.rpow_pos_of_pos hP.1 _
  have hlogpow :
      Real.log (Real.rpow (numericalP preliminaryB r)
        (1 / (1 - preliminaryM r))) =
          (1 / (1 - preliminaryM r)) * Real.log (numericalP preliminaryB r) := by
    simpa only [Real.rpow_eq_pow] using
      Real.log_rpow hP.1 (1 / (1 - preliminaryM r))
  calc
    Real.log (preliminaryX r) = Real.log (1 - preliminaryM r) +
        Real.log (Real.rpow (numericalP preliminaryB r)
          (1 / (1 - preliminaryM r))) := by
      rw [preliminaryX, numericalX, Real.log_mul hOneM.ne' hpow.ne']
    _ = Real.log (1 - preliminaryM r) +
        (1 / (1 - preliminaryM r)) * Real.log (numericalP preliminaryB r) := by
      rw [hlogpow]
    _ = Real.log (1 - preliminaryM r) +
        Real.log (numericalP preliminaryB r) / (1 - preliminaryM r) := by ring

theorem preliminaryU_eq_neg_log_div {r : ℝ} (hr : 0 < r)
    (hM : preliminaryM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP preliminaryB r ∈ Ioo (0 : ℝ) 1) :
    preliminaryU r = -Real.log (preliminaryX r) / r := by
  rw [log_preliminaryX hM hP, numericalP_preliminary_eq hr]
  have hmR : 0 < preliminaryMRatio r := Real.exp_pos _
  have haR : 0 < preliminaryARatio r := by
    exact div_pos (Real.exp_pos _) (by linarith)
  have hden : 1 - r * preliminaryMRatio r ≠ 0 := by
    rw [← preliminaryM_eq_mul_ratio r]
    linarith [hM.2]
  simp only [preliminaryU, preliminaryNegLogOneSubRatio,
    preliminaryM_eq_mul_ratio r, preliminaryA_eq_mul_ratio hr]
  field_simp [hr.ne', hmR.ne', haR.ne', hden]
  ring

theorem preliminaryX_mem_Ioo_of_parameters {r : ℝ}
    (hM : preliminaryM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP preliminaryB r ∈ Ioo (0 : ℝ) 1) :
    preliminaryX r ∈ Ioo (0 : ℝ) 1 := by
  have hden : 0 < 1 - preliminaryM r := sub_pos.mpr hM.2
  have hexponent : 0 < 1 / (1 - preliminaryM r) := one_div_pos.mpr hden
  have hpowPos : 0 < Real.rpow (numericalP preliminaryB r)
      (1 / (1 - preliminaryM r)) := Real.rpow_pos_of_pos hP.1 _
  have hpowLt : Real.rpow (numericalP preliminaryB r)
      (1 / (1 - preliminaryM r)) < 1 :=
    Real.rpow_lt_one hP.1.le hP.2 hexponent
  constructor
  · dsimp [preliminaryX, numericalX]
    exact mul_pos hden hpowPos
  · dsimp [preliminaryX, numericalX]
    calc
      (1 - preliminaryM r) * Real.rpow (numericalP preliminaryB r)
          (1 / (1 - preliminaryM r)) < (1 - preliminaryM r) * 1 :=
        mul_lt_mul_of_pos_left hpowLt hden
      _ < 1 := by linarith [hM.1]

theorem preliminaryZ_eq_one_sub_X_div {r : ℝ} (hr : 0 < r)
    (hM : preliminaryM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP preliminaryB r ∈ Ioo (0 : ℝ) 1) :
    preliminaryZ r = (1 - preliminaryX r) / r := by
  have hlog := preliminaryU_eq_neg_log_div hr hM hP
  have hX := preliminaryX_mem_Ioo_of_parameters hM hP
  have hU : 0 < preliminaryU r := by
    rw [hlog]
    have hlogneg : Real.log (preliminaryX r) < 0 := Real.log_neg hX.1 hX.2
    exact div_pos (neg_pos.mpr hlogneg) hr
  have hExp : Real.exp (-(r * preliminaryU r)) = preliminaryX r := by
    rw [hlog]
    have he : - (r * (-Real.log (preliminaryX r) / r)) =
        Real.log (preliminaryX r) := by
      field_simp [hr.ne']
    rw [he, Real.exp_log hX.1]
  dsimp [preliminaryZ, preliminaryOneSubExpNegRatio]
  rw [hExp]
  field_simp [hr.ne', hU.ne']

/-- Exact algebraic bridge from the original Stage-0 slack to its smooth
normalized form. -/
theorem preliminarySlack_eq_mul_normalized {r : ℝ} (hr : 0 < r)
    (hM : preliminaryM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP preliminaryB r ∈ Ioo (0 : ℝ) 1) :
    preliminarySlack r = r * preliminaryNormalizedSlack r := by
  have hX := preliminaryX_mem_Ioo_of_parameters hM hP
  have hU := preliminaryU_eq_neg_log_div hr hM hP
  have hZeq := preliminaryZ_eq_one_sub_X_div hr hM hP
  have hZ : 0 < preliminaryZ r := by
    rw [hZeq]
    exact div_pos (sub_pos.mpr hX.2) hr
  have hlogX : Real.log (preliminaryX r) = -(r * preliminaryU r) := by
    rw [hU]
    field_simp [hr.ne']
  have hMR : 0 < preliminaryMRatio r := Real.exp_pos _
  have hlogM :
      Real.log (preliminaryM r) = Real.log r - (9 / 10 : ℝ) * r -
        (1 / 20 : ℝ) * r ^ 2 := by
    rw [preliminaryM_eq_mul_ratio r, Real.log_mul hr.ne' hMR.ne']
    dsimp [preliminaryMRatio]
    rw [Real.log_exp]
    ring
  have hOneX : preliminaryY r = r * preliminaryZ r := by
    dsimp [preliminaryY]
    rw [hZeq]
    field_simp [hr.ne']
  have hlogY : Real.log (preliminaryY r) =
      Real.log r + Real.log (preliminaryZ r) := by
    rw [hOneX, Real.log_mul hr.ne' hZ.ne']
  unfold preliminarySlack
  rw [hlogX, hlogM, hlogY]
  dsimp [preliminaryNormalizedSlack, F, entropy, g, gPoly, preliminaryB]
  field_simp [hr.ne']
  ring

end

end RamseyLean

