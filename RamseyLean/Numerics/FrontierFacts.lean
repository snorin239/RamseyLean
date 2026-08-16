import RamseyLean.Numerics.Core
import RamseyLean.Frontier

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

def preliminaryFrontierR (t : ℝ) : ℝ :=
  -(1 / 4 : ℝ) + (2 / 5 : ℝ) * t + (33 / 200 : ℝ) * t ^ 2 -
    (2 / 25 : ℝ) * t ^ 3

def preliminaryFrontierS (t : ℝ) : ℝ :=
  (13 / 40 : ℝ) * t ^ 2 + (17 / 200 : ℝ) * t ^ 3 -
    (2 / 25 : ℝ) * t ^ 4

theorem preliminary_frontier_exponent (t : ℝ) :
    t * FSlope preliminaryB t - F preliminaryB t =
      -Real.log (1 + t) + Real.exp (-t) * preliminaryFrontierS t := by
  dsimp [FSlope, F, entropy, g, gPoly, preliminaryB, preliminaryFrontierS]
  ring

theorem log_frontierA_preliminary (t : ℝ) :
    Real.log (frontierA (FSlope preliminaryB) t) =
      Real.log t - Real.log (1 + t) -
        Real.exp (-t) * preliminaryFrontierR t := by
  rw [log_frontierA]
  dsimp [FSlope, preliminaryB, preliminaryFrontierR]
  ring

theorem log_frontierB_preliminary (t : ℝ) :
    Real.log (frontierB (F preliminaryB) (FSlope preliminaryB) t) =
      -Real.log (1 + t) + Real.exp (-t) * preliminaryFrontierS t := by
  rw [log_frontierB, preliminary_frontier_exponent]

private def preliminaryFrontierGap (t : ℝ) : ℝ :=
  (1 + t) * FSlope preliminaryB t - F preliminaryB t

private theorem hasDerivAt_preliminaryFrontierGap {t : ℝ} (ht : 0 < t) :
    HasDerivAt preliminaryFrontierGap
      ((1 + t) * FCurvature preliminaryB t) t := by
  have h := (((hasDerivAt_const t 1).add (hasDerivAt_id t)).mul
    (hasDerivAt_FSlope (b := preliminaryB) ht)).sub
      (hasDerivAt_F (b := preliminaryB) ht)
  exact h.congr_deriv (by simp)

private theorem continuousOn_preliminaryFrontierGap :
    ContinuousOn preliminaryFrontierGap (Ioc (0 : ℝ) 1) := by
  exact ((continuousOn_const.add continuousOn_id).mul
    (continuousOn_FSlope preliminaryB)).sub (continuousOn_F preliminaryB)

private theorem preliminaryB_mem_parameterRange :
    preliminaryB ∈ Icc finalB preliminaryB := by
  constructor
  · norm_num [finalB, preliminaryB]
  · exact le_rfl

private theorem preliminaryFrontierGap_one :
    preliminaryFrontierGap 1 = (113 / 200 : ℝ) * Real.exp (-1) := by
  norm_num [preliminaryFrontierGap, FSlope, F, entropy, g, gPoly, preliminaryB]
  <;> ring

theorem preliminaryFrontierGap_pos {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryFrontierGap t := by
  have hanti : StrictAntiOn preliminaryFrontierGap (Ioc (0 : ℝ) 1) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioc (0 : ℝ) 1)
      continuousOn_preliminaryFrontierGap
    · intro u hu
      exact (hasDerivAt_preliminaryFrontierGap (interior_subset hu).1).hasDerivWithinAt
    · intro u hu
      have hu' : u ∈ Ioc (0 : ℝ) 1 := interior_subset hu
      exact mul_neg_of_pos_of_neg (by linarith [hu'.1])
        (FCurvature_neg preliminaryB_mem_parameterRange hu')
  have hone : 0 < preliminaryFrontierGap 1 := by
    rw [preliminaryFrontierGap_one]
    positivity
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · exact hone
  · exact hone.trans (hanti ht ⟨by norm_num, le_rfl⟩ hlt)

private theorem preliminaryFrontierS_nonneg {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ preliminaryFrontierS t := by
  have ht0 : 0 ≤ t := ht.1.le
  have ht2le : t ^ 2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht.2)]
  have hfactor : 0 ≤ (13 / 40 : ℝ) + (17 / 200 : ℝ) * t - (2 / 25 : ℝ) * t ^ 2 := by
    nlinarith
  rw [show preliminaryFrontierS t = t ^ 2 *
      ((13 / 40 : ℝ) + (17 / 200 : ℝ) * t - (2 / 25 : ℝ) * t ^ 2) by
        simp [preliminaryFrontierS]; ring]
  positivity

private theorem preliminaryFrontierS_le {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    preliminaryFrontierS t ≤ (41 / 100 : ℝ) * t := by
  have ht0 : 0 ≤ t := ht.1.le
  have ht2le : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht.2)]
  have ht2leOne : t ^ 2 ≤ 1 := ht2le.trans ht.2
  have ht3le : t ^ 3 ≤ t := by
    have := mul_le_mul_of_nonneg_left ht2leOne ht0
    nlinarith
  have ht4 : 0 ≤ t ^ 4 := pow_nonneg ht0 4
  dsimp [preliminaryFrontierS]
  nlinarith

theorem preliminary_frontierB_mem_Ioo {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    frontierB (F preliminaryB) (FSlope preliminaryB) t ∈ Ioo (0 : ℝ) 1 := by
  have hS0 := preliminaryFrontierS_nonneg ht
  have hSle := preliminaryFrontierS_le ht
  have hexp : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [ht.1]
  have hexpS : Real.exp (-t) * preliminaryFrontierS t ≤ preliminaryFrontierS t := by
    nlinarith [Real.exp_pos (-t)]
  have hden : 0 < t + 2 := by linarith [ht.1]
  have hlinear : (41 / 100 : ℝ) * t < 2 * t / (t + 2) := by
    rw [lt_div_iff₀ hden]
    nlinarith [ht.1, ht.2, mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  have hlog : 2 * t / (t + 2) ≤ Real.log (1 + t) :=
    Real.le_log_one_add_of_nonneg ht.1.le
  have hexponent : t * FSlope preliminaryB t - F preliminaryB t < 0 := by
    rw [preliminary_frontier_exponent]
    linarith
  constructor
  · exact Real.exp_pos _
  · rw [frontierB, Real.exp_lt_one_iff]
    exact hexponent

theorem preliminary_frontierA_lt_frontierB {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    frontierA (FSlope preliminaryB) t <
      frontierB (F preliminaryB) (FSlope preliminaryB) t := by
  rw [frontierA, frontierB, Real.exp_lt_exp]
  have hgap := preliminaryFrontierGap_pos ht
  dsimp [preliminaryFrontierGap] at hgap
  linarith

theorem preliminary_frontier_pair_mem
    (hF : UniformRamseyExpBound (F preliminaryB))
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    frontierA (FSlope preliminaryB) t ∈ Ioo (0 : ℝ) 1 ∧
      frontierB (F preliminaryB) (FSlope preliminaryB) t ∈ Ioo (0 : ℝ) 1 ∧
      (frontierA (FSlope preliminaryB) t,
        frontierB (F preliminaryB) (FSlope preliminaryB) t) ∈ asymptoticRegion ∧
      (frontierB (F preliminaryB) (FSlope preliminaryB) t,
        frontierA (FSlope preliminaryB) t) ∈ asymptoticRegion := by
  exact frontier_pair_mem_asymptoticRegion hF
    (strictConcaveOn_F preliminaryB_mem_parameterRange).concaveOn
    (fun u hu => hasDerivAt_F hu.1)
    (fun u hu => FSlope_pos preliminaryB_mem_parameterRange hu)
    (fun u hu => preliminary_frontierB_mem_Ioo hu)
    (fun u hu => preliminary_frontierA_lt_frontierB hu)
    ht

end

end RamseyLean






