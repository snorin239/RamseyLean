import RamseyLean.Numerics.PreliminaryCertificate
import RamseyLean.Numerics.PreliminarySmooth
import RamseyLean.Numerics.Ranges
import RamseyLean.Descent
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Preliminary numerical descent certificate

This module supplies the range, continuity, exact descent-parameter, and
Erdős--Szekeres-region facts for the independently retuned Stage-0 parameters
`b₀ = 3 / 40` and `M₀(r) = r * exp (-(9 / 10)r - (1 / 20)r²)`.
The continuum slack certificate is stated below using the smooth normalization
proved in `Numerics.PreliminarySmooth`.
-/

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

theorem preliminaryX_mem_Ioo {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    preliminaryX r ∈ Ioo (0 : ℝ) 1 := by
  exact numericalX_mem_Ioo
    ⟨by norm_num [finalB, preliminaryB], le_rfl⟩ hr (preliminaryM_mem_Ioo hr)

theorem preliminaryY_mem_Ioo {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    preliminaryY r ∈ Ioo (0 : ℝ) 1 := by
  have hX := preliminaryX_mem_Ioo hr
  dsimp [preliminaryY]
  constructor <;> linarith [hX.1, hX.2]

theorem continuousOn_preliminaryX :
    ContinuousOn preliminaryX (Ioc (0 : ℝ) 1) := by
  intro r hr
  have hM := preliminaryM_mem_Ioo hr
  have hP := numericalP_mem_Ioo
    ⟨by norm_num [finalB, preliminaryB], le_rfl⟩ hr
  have hMcont : ContinuousWithinAt preliminaryM (Ioc (0 : ℝ) 1) r :=
    continuous_preliminaryM.continuousWithinAt
  have hSlopeCont : ContinuousWithinAt (FSlope preliminaryB)
      (Ioc (0 : ℝ) 1) r := continuousOn_FSlope preliminaryB r hr
  have hExpCont : ContinuousWithinAt
      (fun x => Real.exp (-FSlope preliminaryB x)) (Ioc (0 : ℝ) 1) r :=
    Real.continuous_exp.continuousAt.comp_continuousWithinAt hSlopeCont.neg
  have hPcont : ContinuousWithinAt (numericalP preliminaryB)
      (Ioc (0 : ℝ) 1) r := continuousWithinAt_const.sub hExpCont
  have hOneMcont : ContinuousWithinAt (fun x => 1 - preliminaryM x)
      (Ioc (0 : ℝ) 1) r := hMcont.const_sub 1
  unfold preliminaryX numericalX
  exact hOneMcont.mul (hPcont.rpow
    (continuousWithinAt_const.div hOneMcont (by linarith [hM.2]))
    (Or.inl hP.1.ne'))

theorem continuousOn_preliminaryY :
    ContinuousOn preliminaryY (Ioc (0 : ℝ) 1) := by
  unfold preliminaryY
  exact continuousOn_const.sub continuousOn_preliminaryX

theorem preliminaryX_eq_descent (r : ℝ) :
    preliminaryX r =
      (1 - Real.exp (-FSlope preliminaryB r)) ^
        (1 / (1 - preliminaryM r)) * (1 - preliminaryM r) := by
  simpa [preliminaryX] using
    (numericalX_eq_descent (b := preliminaryB) (r := r) (M := preliminaryM))

theorem preliminary_pair_mem_asymptoticRegion {r : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    (preliminaryX r, preliminaryY r) ∈ asymptoticRegion := by
  have hX := preliminaryX_mem_Ioo hr
  simpa [preliminaryY] using
    baseline_mem_asymptoticRegion (preliminaryX r) ⟨hX.1.le, hX.2.le⟩

theorem denseCaseExponent_preliminary_eq (r : ℝ) :
    denseCaseExponent (preliminaryX r) (preliminaryM r) (preliminaryY r) r =
      F preliminaryB r - preliminarySlack r := by
  dsimp [denseCaseExponent, preliminarySlack]
  ring


/-- Paper Lemma `lem:numerics`, preliminary stage: the original descent
slack is strictly positive for every ratio in `(0,1]`. -/
theorem preliminarySlack_pos {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminarySlack r := by
  have hM := preliminaryM_mem_Ioo hr
  have hP := numericalP_mem_Ioo
    ⟨by norm_num [finalB, preliminaryB], le_rfl⟩ hr
  rw [preliminarySlack_eq_mul_normalized hr.1 hM hP]
  exact mul_pos hr.1 (preliminaryNormalizedSlack_pos hr)

/-- The certified preliminary slack gives the strict dense-case inequality
required by the descent theorem. -/
theorem denseCaseExponent_preliminary_lt {r : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    denseCaseExponent (preliminaryX r) (preliminaryM r) (preliminaryY r) r <
      F preliminaryB r := by
  rw [denseCaseExponent_preliminary_eq]
  exact sub_lt_self _ (preliminarySlack_pos hr)

/-- Paper Lemma `lem:numerics`, preliminary descent conclusion for the
independently retuned coefficient `b₀ = 3/40`. -/
theorem uniformRamseyExpBound_preliminary :
    UniformRamseyExpBound (F preliminaryB) := by
  have hb : preliminaryB ∈ Icc finalB preliminaryB :=
    ⟨by norm_num [finalB, preliminaryB], le_rfl⟩
  apply uniformRamseyExpBound_of_descent
      (F := F preliminaryB) (D := FSlope preliminaryB)
      (M := preliminaryM) (X := preliminaryX) (Y := preliminaryY)
  · intro r hr
    exact hasDerivAt_F hr.1
  · exact continuousOn_FSlope preliminaryB
  · exact continuous_preliminaryM.continuousOn
  · intro r hr
    exact (F_pos hb hr).le
  · intro r hr
    exact FSlope_pos hb hr
  · intro r hr
    exact preliminaryM_mem_Ioo hr
  · intro r hr
    exact preliminaryX_mem_Ioo hr
  · intro r hr
    exact preliminaryY_mem_Ioo hr
  · intro r _hr
    exact preliminaryX_eq_descent r
  · intro r hr
    exact preliminary_pair_mem_asymptoticRegion hr
  · intro r hr
    exact denseCaseExponent_preliminary_lt hr

end

end RamseyLean




