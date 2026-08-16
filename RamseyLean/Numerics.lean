import RamseyLean.Numerics.Preliminary
import RamseyLean.Numerics.FinalCertificateConcrete

/-!
# Certified numerical optimization

This module assembles the independently optimized, kernel-checked numerical
input used for paper Theorem `t:main`.  The manuscript's Mathematica
certificate for Lemma `lem:numerics` is not imported as evidence: the
transcendental estimates, interval arithmetic, and every concrete mesh leaf
are proved in Lean from exact rational or integer data.
-/

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

/-- Paper Lemma `lem:numerics`, replaced by an independently optimized
two-stage descent certificate sufficient for the exact exponent in
Theorem `t:main`. -/
theorem uniformRamseyExpBound_final :
    UniformRamseyExpBound (F finalB) := by
  have hb : finalB ∈ Icc finalB preliminaryB :=
    ⟨le_rfl, by norm_num [finalB, preliminaryB]⟩
  apply uniformRamseyExpBound_of_descent
      (F := F finalB) (D := FSlope finalB)
      (M := finalM) (X := finalX) (Y := finalY)
  · intro r hr
    exact hasDerivAt_F hr.1
  · exact continuousOn_FSlope finalB
  · exact continuous_finalM.continuousOn
  · intro r hr
    exact (F_pos hb hr).le
  · intro r hr
    exact FSlope_pos hb hr
  · intro r hr
    exact finalM_mem_Ioo hr
  · intro r hr
    exact finalX_mem_Ioo hr
  · intro r hr
    exact
      (final_descent_of_certificate uniformRamseyExpBound_preliminary
        FinalCertificate.finalNumericalCertificate hr).1
  · intro r _hr
    exact finalX_eq_descent r
  · intro r hr
    exact
      (final_descent_of_certificate uniformRamseyExpBound_preliminary
        FinalCertificate.finalNumericalCertificate hr).2.1
  · intro r hr
    exact
      (final_descent_of_certificate uniformRamseyExpBound_preliminary
        FinalCertificate.finalNumericalCertificate hr).2.2

end

end RamseyLean
