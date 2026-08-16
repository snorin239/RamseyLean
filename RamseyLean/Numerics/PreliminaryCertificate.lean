import RamseyLean.Numerics.PreliminaryCertificateCoverage
import RamseyLean.Numerics.PreliminaryCertificateData

set_option autoImplicit false

namespace RamseyLean

open Set
open FixedPointInterval

noncomputable section

/-- Paper Lemma `lem:numerics`, preliminary stage: the independently retuned
smooth descent slack is strictly positive on the full ratio interval. Every
finite numerical leaf is checked by Lean's kernel using fixed-point interval
arithmetic. -/
theorem preliminaryNormalizedSlack_pos {r : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryNormalizedSlack r := by
  by_cases h0 : r ≤ (3 / 1000 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_of_checkOrigin
      PreliminaryCertificate.Data.Origin.check_true
    · rw [PreliminaryCertificate.Data.Origin.input]
      change value 0 ≤ r ∧ r ≤ value (3 * scale / 1000)
      constructor
      · exact (by simpa [value] using hr.1.le)
      · norm_num [value, scale]
        exact h0
    · exact hr
  by_cases h1 : r ≤ (1 / 10 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := 3 * scale / 1000) (b := scale / 10) (N := 25)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band0
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h2 : r ≤ (1 / 5 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := scale / 10) (b := scale / 5) (N := 50)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band1
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h3 : r ≤ (3 / 10 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := scale / 5) (b := 3 * scale / 10) (N := 125)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band2
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h4 : r ≤ (2 / 5 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := 3 * scale / 10) (b := 2 * scale / 5) (N := 334)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band3
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h5 : r ≤ (1 / 2 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := 2 * scale / 5) (b := scale / 2) (N := 500)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band4
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h6 : r ≤ (3 / 5 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := scale / 2) (b := 3 * scale / 5) (N := 500)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band5
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h7 : r ≤ (4 / 5 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := 3 * scale / 5) (b := 4 * scale / 5) (N := 500)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band6
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  by_cases h8 : r ≤ (4997 / 5000 : ℝ)
  · apply PreliminaryCertificate.normalized_pos_on_affine_band
      (a := 4 * scale / 5) (b := 4997 * scale / 5000) (N := 333)
      (by norm_num [value, scale]) (by norm_num)
      PreliminaryCertificate.Data.All.exists_checked_band7
      (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  · apply PreliminaryCertificate.normalized_pos_of_checkPositive
      PreliminaryCertificate.Data.Terminal.check_true
    · rw [PreliminaryCertificate.Data.Terminal.input]
      change value (4997 * scale / 5000) ≤ r ∧ r ≤ value scale
      constructor
      · norm_num [value, scale]
        linarith
      · norm_num [value, scale]
        exact hr.2
    · exact hr

end

end RamseyLean
