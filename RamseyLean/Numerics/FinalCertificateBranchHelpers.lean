import RamseyLean.Numerics.FinalCertificateProof

/-! Shared polynomial soundness lemmas for final numerical branch certificates. -/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open FixedPointInterval

noncomputable section

theorem mulNonneg_lo_nonneg {I J : Interval}
    (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) : 0 ≤ (mulNonneg I J).lo := by
  simp only [mulNonneg, down]
  exact Int.ediv_nonneg (mul_nonneg hI hJ) (by norm_num [scale])

theorem preliminaryR_contains {I : Interval} {x : ℝ}
    (hx : I.Contains x) (hI : 0 ≤ I.lo) :
    (preliminaryR I).Contains (preliminaryFrontierR x) := by
  let I2 := mulNonneg I I
  let I3 := mulNonneg I2 I
  have hI2 : I2.Contains (x ^ 2) := by
    dsimp [I2]
    simpa only [pow_two] using hx.mulNonneg hx hI hI
  have hI2lo : 0 ≤ I2.lo := by
    dsimp [I2]
    exact mulNonneg_lo_nonneg hI hI
  have hI3 : I3.Contains (x ^ 3) := by
    dsimp [I3]
    have h := hI2.mulNonneg hx hI2lo hI
    convert h using 1 <;> ring
  have hq : (rationalInterval (-1) 4).Contains (-(1 / 4 : ℝ)) := by
    convert rationalInterval_contains (-1) (q := 4) (by norm_num) using 1 <;>
      norm_num
  have h2 : (rationalInterval 2 5).Contains (2 / 5 : ℝ) :=
    rationalInterval_contains 2 (q := 5) (by norm_num)
  have h33 : (rationalInterval 33 200).Contains (33 / 200 : ℝ) :=
    rationalInterval_contains 33 (q := 200) (by norm_num)
  have hn2 : (rationalInterval (-2) 25).Contains (-(2 / 25 : ℝ)) := by
    convert rationalInterval_contains (-2) (q := 25) (by norm_num) using 1 <;>
      norm_num
  have h := ((hq.add (h2.mul hx)).add (h33.mul hI2)).add (hn2.mul hI3)
  rw [show preliminaryR I =
    add (add (add (rationalInterval (-1) 4) (mul (rationalInterval 2 5) I))
      (mul (rationalInterval 33 200) I2)) (mul (rationalInterval (-2) 25) I3) by
      rfl]
  convert h using 1 <;> simp only [preliminaryFrontierR] <;> ring

theorem preliminaryS_contains {I : Interval} {x : ℝ}
    (hx : I.Contains x) (hI : 0 ≤ I.lo) :
    (preliminaryS I).Contains (preliminaryFrontierS x) := by
  let I2 := mulNonneg I I
  let I3 := mulNonneg I2 I
  let I4 := mulNonneg I3 I
  have hI2 : I2.Contains (x ^ 2) := by
    dsimp [I2]
    simpa only [pow_two] using hx.mulNonneg hx hI hI
  have hI2lo : 0 ≤ I2.lo := by
    dsimp [I2]
    exact mulNonneg_lo_nonneg hI hI
  have hI3 : I3.Contains (x ^ 3) := by
    dsimp [I3]
    have h := hI2.mulNonneg hx hI2lo hI
    convert h using 1 <;> ring
  have hI3lo : 0 ≤ I3.lo := by
    dsimp [I3]
    exact mulNonneg_lo_nonneg hI2lo hI
  have hI4 : I4.Contains (x ^ 4) := by
    dsimp [I4]
    have h := hI3.mulNonneg hx hI3lo hI
    convert h using 1 <;> ring
  have h13 : (rationalInterval 13 40).Contains (13 / 40 : ℝ) :=
    rationalInterval_contains 13 (q := 40) (by norm_num)
  have h17 : (rationalInterval 17 200).Contains (17 / 200 : ℝ) :=
    rationalInterval_contains 17 (q := 200) (by norm_num)
  have hn2 : (rationalInterval (-2) 25).Contains (-(2 / 25 : ℝ)) := by
    convert rationalInterval_contains (-2) (q := 25) (by norm_num) using 1 <;>
      norm_num
  have h := ((h13.mul hI2).add (h17.mul hI3)).add (hn2.mul hI4)
  rw [show preliminaryS I =
    add (add (mul (rationalInterval 13 40) I2) (mul (rationalInterval 17 200) I3))
      (mul (rationalInterval (-2) 25) I4) by rfl]
  convert h using 1 <;> simp only [preliminaryFrontierS] <;> ring

theorem correction_contains {I I2 E : Interval} {r : ℝ}
    (hr : I.Contains r) (hr2 : I2.Contains (r ^ 2))
    (he : E.Contains (Real.exp (-r))) :
    (correction I I2 E).Contains
      (Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
        (2 / 25 : ℝ) * r ^ 2)) := by
  have hq : (rationalInterval (-1) 4).Contains (-(1 / 4 : ℝ)) := by
    convert rationalInterval_contains (-1) (q := 4) (by norm_num) using 1 <;>
      norm_num
  have h3 : (rationalInterval 3 100).Contains (3 / 100 : ℝ) :=
    rationalInterval_contains 3 (q := 100) (by norm_num)
  have h2 : (rationalInterval 2 25).Contains (2 / 25 : ℝ) :=
    rationalInterval_contains 2 (q := 25) (by norm_num)
  exact he.mul ((hq.add (h3.mul hr)).add (h2.mul hr2))

theorem commonTail_contains {I I2 U : Interval} {r u : ℝ}
    (hr : I.Contains r) (hr2 : I2.Contains (r ^ 2)) (hu : U.Contains u) :
    (commonTail I I2 U).Contains
      (-u / 2 - (7 / 20 : ℝ) * r - (13 / 100 : ℝ) * r ^ 2) := by
  have hn7 : (rationalInterval (-7) 20).Contains (-(7 / 20 : ℝ)) := by
    convert rationalInterval_contains (-7) (q := 20) (by norm_num) using 1 <;>
      norm_num
  have hn13 : (rationalInterval (-13) 100).Contains (-(13 / 100 : ℝ)) := by
    convert rationalInterval_contains (-13) (q := 100) (by norm_num) using 1 <;>
      norm_num
  have h := ((hu.divNat (by norm_num : 0 < 2)).neg.add (hn7.mul hr)).add
    (hn13.mul hr2)
  rw [show commonTail I I2 U =
    add (add (neg (divNat U 2)) (mul (rationalInterval (-7) 20) I))
      (mul (rationalInterval (-13) 100) I2) by rfl]
  convert h using 1 <;> ring

end

end RamseyLean.FinalCertificate
