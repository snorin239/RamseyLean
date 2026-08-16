import RamseyLean.Numerics.FinalCertificateRouting
import RamseyLean.Numerics.FinalCertificateData

/-!
# Concrete final numerical certificate

The generated fixed-point literals instantiate every row source required by
the continuum routing theorem.  Consequently all region and strict-slack
fields of `FinalNumericalCertificate` are proved without trusted external
numerical computation.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

noncomputable section

/-- Every cell of the independently selected final meshes has a
kernel-checked literal row. -/
theorem finalRowCertificate : FinalRowCertificate where
  smallSeries := Data.exists_checked_smallSeries
  smallQuotientA := Data.exists_checked_smallQuotientA
  smallQuotientB := Data.exists_checked_smallQuotientB
  middle := Data.exists_checked_middle
  cap := Data.exists_checked_cap
  large0 := Data.exists_checked_large0
  large1 := Data.exists_checked_large1
  large2 := Data.exists_checked_large2
  large3 := Data.exists_checked_large3
  crossingCoarse := Data.exists_checked_crossingCoarse
  crossingFineB := Data.exists_checked_crossingFineB
  crossingFineBUpper := Data.exists_checked_crossingFineBUpper
  crossingFineALower := Data.exists_checked_crossingFineALower
  crossingFineA := Data.exists_checked_crossingFineA

/-- Paper Lemma `lem:numerics`, final stage: the complete checked numerical
certificate for the descent from `preliminaryB` to `finalB`. -/
theorem finalNumericalCertificate : FinalNumericalCertificate :=
  finalNumericalCertificate_of_rows finalRowCertificate

end

end RamseyLean.FinalCertificate
