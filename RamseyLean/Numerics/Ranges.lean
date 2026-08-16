import RamseyLean.Numerics.Core

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

theorem preliminaryM_mem_Ioo {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    preliminaryM r ∈ Ioo (0 : ℝ) 1 := by
  have hexponent : -(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2 < 0 := by
    nlinarith [hr.1, sq_nonneg r]
  have he : Real.exp (-(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact hexponent
  constructor
  · exact mul_pos hr.1 (Real.exp_pos _)
  · change r * Real.exp (-(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2) < 1
    calc
      r * Real.exp (-(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2) < r * 1 :=
        mul_lt_mul_of_pos_left he hr.1
      _ ≤ 1 := by simpa using hr.2

theorem finalM_mem_Ioo {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    finalM r ∈ Ioo (0 : ℝ) 1 := by
  have hexponent : -(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2 < 0 := by
    nlinarith [hr.1, sq_nonneg r]
  have he : Real.exp (-(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact hexponent
  constructor
  · exact mul_pos hr.1 (Real.exp_pos _)
  · change r * Real.exp (-(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2) < 1
    calc
      r * Real.exp (-(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2) < r * 1 :=
        mul_lt_mul_of_pos_left he hr.1
      _ ≤ 1 := by simpa using hr.2

theorem continuous_preliminaryM : Continuous preliminaryM := by
  unfold preliminaryM
  fun_prop

theorem continuous_finalM : Continuous finalM := by
  unfold finalM
  fun_prop

theorem numericalP_mem_Ioo {b r : ℝ}
    (hb : b ∈ Icc finalB preliminaryB) (hr : r ∈ Ioc (0 : ℝ) 1) :
    numericalP b r ∈ Ioo (0 : ℝ) 1 := by
  have hslope := FSlope_pos hb hr
  constructor
  · dsimp [numericalP]
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  · dsimp [numericalP]
    linarith [Real.exp_pos (-FSlope b r)]

theorem numericalX_mem_Ioo {b r : ℝ} {M : ℝ → ℝ}
    (hb : b ∈ Icc finalB preliminaryB) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hM : M r ∈ Ioo (0 : ℝ) 1) :
    numericalX b M r ∈ Ioo (0 : ℝ) 1 := by
  have hP := numericalP_mem_Ioo hb hr
  have hbase : 1 - M r ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hM.1, hM.2]
  have hexponent : 0 < 1 / (1 - M r) := one_div_pos.mpr hbase.1
  have hpowpos : 0 < Real.rpow (numericalP b r) (1 / (1 - M r)) :=
    Real.rpow_pos_of_pos hP.1 _
  have hpowlt : Real.rpow (numericalP b r) (1 / (1 - M r)) < 1 :=
    Real.rpow_lt_one hP.1.le hP.2 hexponent
  constructor
  · exact mul_pos hbase.1 hpowpos
  · change (1 - M r) * Real.rpow (numericalP b r) (1 / (1 - M r)) < 1
    calc
      (1 - M r) * Real.rpow (numericalP b r) (1 / (1 - M r)) <
          1 * Real.rpow (numericalP b r) (1 / (1 - M r)) :=
        mul_lt_mul_of_pos_right hbase.2 hpowpos
      _ < 1 := by simpa using hpowlt

theorem numericalX_eq_descent {b r : ℝ} {M : ℝ → ℝ} :
    numericalX b M r =
      (1 - Real.exp (-FSlope b r)) ^ (1 / (1 - M r)) * (1 - M r) := by
  simp [numericalX, numericalP, mul_comm]

end

end RamseyLean


