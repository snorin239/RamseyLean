import RamseyLean.AsymptoticRegion
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# The concave Ramsey frontier

This module formalizes the reusable content of paper Lemma `lem:frontier`.
The manuscript's phrases "increases from `0`" and "decreases from `1`" are
represented in the final theorem by the exact preimage hypotheses needed for
the two inverse branches.  This avoids choosing a particular inverse API while
retaining the printed piecewise frontier function.
-/

set_option autoImplicit false

namespace RamseyLean

open Set

/-- The function `A(t) = exp (-f'(t))` from paper Lemma `lem:frontier`, with
the derivative represented by the explicit slope function `D`. -/
noncomputable def frontierA (D : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-D t)

/-- The function `B(t) = exp (t f'(t) - f(t))` from paper Lemma
`lem:frontier`. -/
noncomputable def frontierB (F D : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t * D t - F t)

/-- A chosen parameter in the `A`-branch of the frontier.  It is used only at
points for which a preimage in `(0,1]` is supplied by the hypotheses of
`frontier_mem_asymptoticRegion`. -/
noncomputable def frontierAParameter (D : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ t ∈ Ioc (0 : ℝ) 1, frontierA D t = x then Classical.choose h else 1

/-- A chosen parameter in the `B`-branch of the frontier. -/
noncomputable def frontierBParameter (F D : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ t ∈ Ioc (0 : ℝ) 1, frontierB F D t = x then Classical.choose h else 1

/-- The three-part function `Y_f` from equation `eq:frontier` in the paper.
The outer parameters are selected noncomputably from the corresponding level
sets; the theorem below supplies those level sets on exactly the needed
intervals. -/
noncomputable def frontierY (F D : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < frontierA D 1 then
    frontierB F D (frontierAParameter D x)
  else if x ≤ frontierB F D 1 then
    Real.exp (-F 1) / x
  else
    frontierA D (frontierBParameter F D x)

@[simp]
theorem log_frontierA (D : ℝ → ℝ) (t : ℝ) :
    Real.log (frontierA D t) = -D t := by
  simp [frontierA]

@[simp]
theorem log_frontierB (F D : ℝ → ℝ) (t : ℝ) :
    Real.log (frontierB F D t) = t * D t - F t := by
  simp [frontierB]

/-- The two endpoint coordinates have the product used by the middle branch. -/
theorem frontierA_mul_frontierB_one (F D : ℝ → ℝ) :
    frontierA D 1 * frontierB F D 1 = Real.exp (-F 1) := by
  rw [frontierA, frontierB, ← Real.exp_add]
  congr 1
  ring

/-- Rewrite the closed middle branch of the frontier. -/
theorem frontierY_eq_middle {F D : ℝ → ℝ} {x : ℝ}
    (hAx : frontierA D 1 ≤ x) (hxB : x ≤ frontierB F D 1) :
    frontierY F D x = Real.exp (-F 1) / x := by
  rw [frontierY, if_neg (not_lt.mpr hAx), if_pos hxB]

private theorem frontierAParameter_spec {D : ℝ → ℝ} {x : ℝ}
    (h : ∃ t ∈ Ioc (0 : ℝ) 1, frontierA D t = x) :
    frontierAParameter D x ∈ Ioc (0 : ℝ) 1 ∧
      frontierA D (frontierAParameter D x) = x := by
  rw [frontierAParameter, dif_pos h]
  exact Classical.choose_spec h

private theorem frontierBParameter_spec {F D : ℝ → ℝ} {x : ℝ}
    (h : ∃ t ∈ Ioc (0 : ℝ) 1, frontierB F D t = x) :
    frontierBParameter F D x ∈ Ioc (0 : ℝ) 1 ∧
      frontierB F D (frontierBParameter F D x) = x := by
  rw [frontierBParameter, dif_pos h]
  exact Classical.choose_spec h

/-- Expose the parameter equation chosen by the left branch.  This relational
form is intended for later kernel-checked numerical estimates. -/
theorem exists_frontierY_left_parameter {F D : ℝ → ℝ} {x : ℝ}
    (hx : x < frontierA D 1)
    (hpre : ∃ t ∈ Ioc (0 : ℝ) 1, frontierA D t = x) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      frontierA D t = x ∧ frontierY F D x = frontierB F D t := by
  classical
  have hspec := frontierAParameter_spec hpre
  refine ⟨frontierAParameter D x, hspec.1, hspec.2, ?_⟩
  simp [frontierY, hx]

/-- Expose the parameter equation chosen by the right branch. -/
theorem exists_frontierY_right_parameter {F D : ℝ → ℝ} {x : ℝ}
    (hAx : frontierA D 1 ≤ x) (hBx : frontierB F D 1 < x)
    (hpre : ∃ t ∈ Ioc (0 : ℝ) 1, frontierB F D t = x) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      frontierB F D t = x ∧ frontierY F D x = frontierA D t := by
  classical
  have hspec := frontierBParameter_spec hpre
  refine ⟨frontierBParameter F D x, hspec.1, hspec.2, ?_⟩
  simp [frontierY, not_lt.mpr hAx, not_le.mpr hBx]

/-- A differentiable concave function lies below each of its tangent lines.
This is the analytic step used twice in paper Lemma `lem:frontier`. -/
theorem concaveOn_le_tangentLine {F D : ℝ → ℝ} {s t : ℝ}
    (hconcave : ConcaveOn ℝ (Ioc (0 : ℝ) 1) F)
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hderiv : HasDerivAt F (D t) t) :
    F s ≤ F t + (s - t) * D t := by
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hslope := hconcave.le_slope_of_hasDerivAt hs ht hst hderiv
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hst)).mp hslope
    nlinarith
  · simp
  · have hslope := hconcave.slope_le_of_hasDerivAt ht hs hts hderiv
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ (sub_pos.mpr hts)).mp hslope
    nlinarith

/-- The two ordered frontier points associated to one tangent parameter lie in
the asymptotic Ramsey region.  This is the first, and downstream-most useful,
part of paper Lemma `lem:frontier`. -/
theorem frontier_pair_mem_asymptoticRegion
    {F D : ℝ → ℝ}
    (hF : UniformRamseyExpBound F)
    (hconcave : ConcaveOn ℝ (Ioc (0 : ℝ) 1) F)
    (hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (D t) t)
    (hDpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < D t)
    (hBunit : ∀ t ∈ Ioc (0 : ℝ) 1, frontierB F D t ∈ Ioo (0 : ℝ) 1)
    (hAB : ∀ t ∈ Ioc (0 : ℝ) 1, frontierA D t < frontierB F D t)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    frontierA D t ∈ Ioo (0 : ℝ) 1 ∧
      frontierB F D t ∈ Ioo (0 : ℝ) 1 ∧
      (frontierA D t, frontierB F D t) ∈ asymptoticRegion ∧
      (frontierB F D t, frontierA D t) ∈ asymptoticRegion := by
  have hAunit : frontierA D t ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨Real.exp_pos _, ?_⟩
    rw [frontierA, Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (hDpos t ht)
  have hBtunit := hBunit t ht
  have hgap : 0 < (1 + t) * D t - F t := by
    have hexp : -D t < t * D t - F t := by
      simpa only [frontierA, frontierB, Real.exp_lt_exp] using hAB t ht
    linarith
  have hBA (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      F s ≤ -Real.log (frontierB F D t) - s * Real.log (frontierA D t) := by
    calc
      F s ≤ F t + (s - t) * D t :=
        concaveOn_le_tangentLine hconcave hs ht (hderiv t ht)
      _ = -Real.log (frontierB F D t) -
            s * Real.log (frontierA D t) := by
        simp only [frontierA, frontierB, Real.log_exp]
        ring
  have hABound (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      F s ≤ -Real.log (frontierA D t) - s * Real.log (frontierB F D t) := by
    have hnonneg : 0 ≤ (1 - s) * ((1 + t) * D t - F t) :=
      mul_nonneg (sub_nonneg.mpr hs.2) hgap.le
    calc
      F s ≤ F t + (s - t) * D t :=
        concaveOn_le_tangentLine hconcave hs ht (hderiv t ht)
      _ ≤ -Real.log (frontierA D t) -
            s * Real.log (frontierB F D t) := by
        simp only [frontierA, frontierB, Real.log_exp]
        nlinarith
  refine ⟨hAunit, hBtunit, ?_, ?_⟩
  · exact mem_asymptoticRegion_of_uniform_bound hAunit hBtunit hF hABound hBA
  · exact mem_asymptoticRegion_of_uniform_bound hBtunit hAunit hF hBA hABound

/-- The hyperbolic middle segment joining `(A(1),B(1))` to its transpose lies
in the asymptotic Ramsey region.  This is the middle case of paper Lemma
`lem:frontier`. -/
theorem frontier_middle_mem_asymptoticRegion
    {F D : ℝ → ℝ}
    (hF : UniformRamseyExpBound F)
    (hconcave : ConcaveOn ℝ (Ioc (0 : ℝ) 1) F)
    (hderivOne : HasDerivAt F (D 1) 1)
    (hAunit : frontierA D 1 ∈ Ioo (0 : ℝ) 1)
    (hBunit : frontierB F D 1 ∈ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (frontierA D 1) (frontierB F D 1)) :
    Real.exp (-F 1) / x ∈ Ioo (0 : ℝ) 1 ∧
      (x, Real.exp (-F 1) / x) ∈ asymptoticRegion := by
  let a := frontierA D 1
  let b := frontierB F D 1
  let y := Real.exp (-F 1) / x
  have hxpos : 0 < x := hAunit.1.trans_le hx.1
  have hab : a * b = Real.exp (-F 1) := by
    dsimp [a, b, frontierA, frontierB]
    rw [← Real.exp_add]
    congr 1
    ring
  have hyEq : y = a * b / x := by
    dsimp [y]
    rw [← hab]
  have hay : a ≤ y := by
    rw [hyEq]
    exact (le_div_iff₀ hxpos).2 (mul_le_mul_of_nonneg_left hx.2 hAunit.1.le)
  have hyb : y ≤ b := by
    rw [hyEq]
    apply (div_le_iff₀ hxpos).2
    calc
      a * b = b * a := mul_comm _ _
      _ ≤ b * x := mul_le_mul_of_nonneg_left hx.1 hBunit.1.le
  have hyunit : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hAunit.1.trans_le hay, hyb.trans_lt hBunit.2⟩
  have hlogxB : Real.log x ≤ D 1 - F 1 := by
    calc
      Real.log x ≤ Real.log b := Real.log_le_log hxpos hx.2
      _ = D 1 - F 1 := by simp [b, frontierB]
  have hlogAx : -D 1 ≤ Real.log x := by
    calc
      -D 1 = Real.log a := by simp [a, frontierA]
      _ ≤ Real.log x := Real.log_le_log hAunit.1 hx.1
  have hlogy : Real.log y = -F 1 - Real.log x := by
    dsimp [y]
    rw [Real.log_div (Real.exp_ne_zero _) hxpos.ne', Real.log_exp]
  have hxy (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      F s ≤ -Real.log x - s * Real.log y := by
    have htangent := concaveOn_le_tangentLine hconcave hs
      (by constructor <;> norm_num) hderivOne
    have hprod : 0 ≤ (s - 1) * (F 1 + Real.log x - D 1) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hs.2) (by linarith)
    rw [hlogy]
    nlinarith
  have hyx (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      F s ≤ -Real.log y - s * Real.log x := by
    have htangent := concaveOn_le_tangentLine hconcave hs
      (by constructor <;> norm_num) hderivOne
    have hprod : 0 ≤ (1 - s) * (Real.log x + D 1) :=
      mul_nonneg (sub_nonneg.mpr hs.2) (by linarith)
    rw [hlogy]
    nlinarith
  refine ⟨hyunit, ?_⟩
  exact mem_asymptoticRegion_of_uniform_bound ⟨hxpos, hx.2.trans_lt hBunit.2⟩
    hyunit hF hxy hyx

/-- Paper Lemma `lem:frontier`.  The manuscript's monotone endpoint language is
encoded by `hAonto` and `hBonto`, which state directly that the two outer
intervals have the required level-set parameters.  The conclusion includes
both assertions in the printed lemma: `Y_f(x) ∈ (0,1)` and frontier membership.
-/
theorem frontier_mem_asymptoticRegion
    {F D : ℝ → ℝ}
    (hF : UniformRamseyExpBound F)
    (hconcave : StrictConcaveOn ℝ (Ioc (0 : ℝ) 1) F)
    (hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (D t) t)
    (hDpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < D t)
    (hBunit : ∀ t ∈ Ioc (0 : ℝ) 1, frontierB F D t ∈ Ioo (0 : ℝ) 1)
    (hAB : ∀ t ∈ Ioc (0 : ℝ) 1, frontierA D t < frontierB F D t)
    (hAonto : ∀ x ∈ Ioo (0 : ℝ) (frontierA D 1),
      ∃ t ∈ Ioc (0 : ℝ) 1, frontierA D t = x)
    (hBonto : ∀ x ∈ Ioo (frontierB F D 1) 1,
      ∃ t ∈ Ioc (0 : ℝ) 1, frontierB F D t = x)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    frontierY F D x ∈ Ioo (0 : ℝ) 1 ∧
      (x, frontierY F D x) ∈ asymptoticRegion := by
  classical
  by_cases hleft : x < frontierA D 1
  · have hspec := frontierAParameter_spec (hAonto x ⟨hx.1, hleft⟩)
    rcases frontier_pair_mem_asymptoticRegion hF hconcave.concaveOn hderiv hDpos
        hBunit hAB hspec.1 with ⟨_, hB, hmem, _⟩
    rw [frontierY, if_pos hleft]
    exact ⟨hB, by simpa [hspec.2] using hmem⟩
  by_cases hmiddle : x ≤ frontierB F D 1
  · have hAone : frontierA D 1 ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨Real.exp_pos _, ?_⟩
      rw [frontierA, Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr (hDpos 1 (by constructor <;> norm_num))
    have hmiddleResult := frontier_middle_mem_asymptoticRegion hF hconcave.concaveOn
      (hderiv 1 (by constructor <;> norm_num)) hAone
      (hBunit 1 (by constructor <;> norm_num)) ⟨le_of_not_gt hleft, hmiddle⟩
    simpa [frontierY, hleft, hmiddle] using hmiddleResult
  · have hspec := frontierBParameter_spec (hBonto x ⟨lt_of_not_ge hmiddle, hx.2⟩)
    rcases frontier_pair_mem_asymptoticRegion hF hconcave.concaveOn hderiv hDpos
        hBunit hAB hspec.1 with ⟨hA, _, _, hmem⟩
    rw [frontierY, if_neg hleft, if_neg hmiddle]
    exact ⟨hA, by simpa [hspec.2] using hmem⟩

end RamseyLean
