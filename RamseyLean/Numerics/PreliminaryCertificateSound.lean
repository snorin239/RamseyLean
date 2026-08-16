import RamseyLean.Numerics.PreliminaryCertificateChecker
import RamseyLean.Numerics.PreliminarySmooth
import RamseyLean.Numerics.Ranges

set_option autoImplicit false

namespace RamseyLean.PreliminaryCertificate

open Set
open FixedPointInterval

noncomputable section

private theorem point_value (z : ℤ) : (point z).Contains (value z) :=
  Interval.contains_point z

private theorem point_one : (point scale).Contains (1 : ℝ) := by
  convert point_value scale using 1 <;> norm_num [value, scale]

structure RestSafety (B : Data) : Prop where
  rNonneg : nonneg B.r = true
  r2Nonneg : nonneg B.r2 = true
  negRExp : expSafe 10 B.negR = true
  mExponentExp : expSafe 10 B.mExponent = true
  mRatioNonneg : nonneg B.mRatio = true
  mNonneg : nonneg B.m = true
  aInnerExp : expSafe 10 B.aInner = true
  onePlusRPos : positive B.onePlusR = true
  aExpNonneg : nonneg B.aExp = true
  invOnePlusRNonneg : nonneg B.invOnePlusR = true
  aRatioNonneg : nonneg B.aRatio = true
  aNonneg : nonneg B.a = true
  mT : qtSafe 12 B.m = true
  aT : qtSafe 12 B.a = true
  tmNonneg : nonneg B.tm = true
  taNonneg : nonneg B.ta = true
  oneMinusMPos : positive B.oneMinusM = true
  invOneMinusMNonneg : nonneg B.invOneMinusM = true
  uLeftNonneg : nonneg B.uLeft = true
  uRight0Nonneg : nonneg B.uRight0 = true
  uRightNonneg : nonneg B.uRight = true
  uNonneg : nonneg B.u = true
  vE : eSafe 10 B.v = true
  evNonneg : nonneg B.ev = true
  zNonneg : nonneg B.z = true
  zPos : positive B.z = true
  zLog : logSafe 10 B.z = true

theorem RestSafety.of_check {B : Data} (h : restSafe B = true) :
    RestSafety B := by
  constructor <;> simp_all only [restSafe, Bool.and_eq_true]

structure EntropySafety (H : EntropyData) : Prop where
  aPos : positive H.a = true
  onePlusAPos : positive H.onePlusA = true
  invANonneg : nonneg H.invA = true
  factorNonneg : nonneg H.factor = true
  onePlusALog : logSafe 10 H.onePlusA = true
  logANonneg : nonneg H.logA = true

theorem EntropySafety.of_check {H : EntropyData}
    (h : entropySafe H = true) : EntropySafety H := by
  constructor <;> simp_all only [entropySafe, Bool.and_eq_true]

private theorem preliminaryU_pos {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryU r := by
  have hM := preliminaryM_mem_Ioo hr
  have hP := numericalP_mem_Ioo
    ⟨by norm_num [finalB, preliminaryB], le_rfl⟩ hr
  have hX := preliminaryX_mem_Ioo_of_parameters hM hP
  rw [preliminaryU_eq_neg_log_div hr.1 hM hP]
  exact div_pos (neg_pos.mpr (Real.log_neg hX.1 hX.2)) hr.1

set_option maxHeartbeats 0 in
theorem u_contains {I : Interval} {B : Data} {r : ℝ}
    (hvalid : RestValid I B) (hsafe : RestSafety B)
    (hrI : I.Contains r) (hr : r ∈ Ioc (0 : ℝ) 1) :
    B.u.Contains (preliminaryU r) := by
  have hR0 : 0 ≤ B.r.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.rNonneg
  have hR20 : 0 ≤ B.r2.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.r2Nonneg
  have hMR0 : 0 ≤ B.mRatio.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.mRatioNonneg
  have hAExp0 : 0 ≤ B.aExp.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.aExpNonneg
  have hInvOne0 : 0 ≤ B.invOnePlusR.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.invOnePlusRNonneg
  have hARatio0 : 0 ≤ B.aRatio.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.aRatioNonneg
  have hTm0 : 0 ≤ B.tm.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.tmNonneg
  have hTa0 : 0 ≤ B.ta.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.taNonneg
  have hInvM0 : 0 ≤ B.invOneMinusM.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.invOneMinusMNonneg
  have hURight00 : 0 ≤ B.uRight0.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.uRight0Nonneg
  have hR : B.r.Contains r := by rw [hvalid.r]; exact hrI
  have hR2 : B.r2.Contains (r ^ 2) := by
    rw [hvalid.r2, pow_two]
    exact hR.mulNonneg hR hR0 hR0
  have hR3 : B.r3.Contains (r ^ 3) := by
    rw [hvalid.r3, pow_succ]
    exact hR2.mulNonneg hR hR20 hR0
  have hNegQuarter : (point (-(scale / 4))).Contains (-(1 / 4 : ℝ)) := by
    convert point_value (-(scale / 4)) using 1 <;> norm_num [value, scale]
  have hTwoFifth : (point (2 * scale / 5)).Contains (2 / 5 : ℝ) := by
    convert point_value (2 * scale / 5) using 1 <;> norm_num [value, scale]
  have hThirtyThree :
      (point (33 * scale / 200)).Contains (33 / 200 : ℝ) := by
    convert point_value (33 * scale / 200) using 1 <;> norm_num [value, scale]
  have hNegTwoTwentyFive :
      (point (-(2 * scale / 25))).Contains (-(2 / 25 : ℝ)) := by
    convert point_value (-(2 * scale / 25)) using 1 <;> norm_num [value, scale]
  have hRemainder : B.remainder.Contains (preliminaryRemainder r) := by
    rw [hvalid.remainder]
    unfold preliminaryRemainder
    convert ((hNegQuarter.add (hTwoFifth.mul hR)).add
      (hThirtyThree.mul hR2)).add (hNegTwoTwentyFive.mul hR3) using 1 <;> ring
  have hNegR : B.negR.Contains (-r) := by
    rw [hvalid.negR]
    exact hR.neg
  have hExpNegR : B.expNegR.Contains (Real.exp (-r)) := by
    rw [hvalid.expNegR]
    exact Sound.contains_exp_of_safe hNegR hsafe.negRExp
  have hNegNineTen :
      (point (-(9 * scale / 10))).Contains (-(9 / 10 : ℝ)) := by
    convert point_value (-(9 * scale / 10)) using 1 <;> norm_num [value, scale]
  have hNegOneTwenty :
      (point (-(scale / 20))).Contains (-(1 / 20 : ℝ)) := by
    convert point_value (-(scale / 20)) using 1 <;> norm_num [value, scale]
  have hMExponent : B.mExponent.Contains
      (-(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2) := by
    rw [hvalid.mExponent]
    convert (hNegNineTen.mul hR).add (hNegOneTwenty.mul hR2) using 1 <;> ring
  have hMRatio : B.mRatio.Contains (preliminaryMRatio r) := by
    rw [hvalid.mRatio]
    simpa only [preliminaryMRatio] using
      Sound.contains_exp_of_safe hMExponent hsafe.mExponentExp
  have hM : B.m.Contains (preliminaryM r) := by
    rw [hvalid.m, preliminaryM_eq_mul_ratio]
    exact hR.mulNonneg hMRatio hR0 hMR0
  have hAInner : B.aInner.Contains
      (-Real.exp (-r) * preliminaryRemainder r) := by
    rw [hvalid.aInner]
    convert (hExpNegR.mul hRemainder).neg using 1 <;> ring
  have hAExp : B.aExp.Contains
      (Real.exp (-Real.exp (-r) * preliminaryRemainder r)) := by
    rw [hvalid.aExp]
    exact Sound.contains_exp_of_safe hAInner hsafe.aInnerExp
  have hOnePlus : B.onePlusR.Contains (1 + r) := by
    rw [hvalid.onePlusR]
    exact point_one.add hR
  have hOnePlusPos : 0 < B.onePlusR.lo := by
    simpa only [positive, decide_eq_true_eq] using hsafe.onePlusRPos
  have hInvOnePlus : B.invOnePlusR.Contains ((1 + r)⁻¹) := by
    rw [hvalid.invOnePlusR]
    exact hOnePlus.inv hOnePlusPos
  have hARatio : B.aRatio.Contains (preliminaryARatio r) := by
    rw [hvalid.aRatio]
    simpa only [preliminaryARatio, div_eq_mul_inv] using
      hAExp.mulNonneg hInvOnePlus hAExp0 hInvOne0
  have hA : B.a.Contains (preliminaryA r) := by
    rw [hvalid.a, preliminaryA_eq_mul_ratio hr.1]
    exact hR.mulNonneg hARatio hR0 hARatio0
  have hMRange := preliminaryM_mem_Ioo hr
  have hAPos : 0 < preliminaryA r := by
    unfold preliminaryA
    exact mul_pos (div_pos hr.1 (by linarith [hr.1])) (Real.exp_pos _)
  have hTmRaw := Sound.contains_t_of_safe hM hsafe.mT
  have hTaRaw := Sound.contains_t_of_safe hA hsafe.aT
  have hTm : B.tm.Contains
      (preliminaryNegLogOneSubRatio (preliminaryM r)) := by
    rw [CertifiedNumerics.negLogOneSubRatio_eq_of_ne hMRange.1.ne'] at hTmRaw
    rw [hvalid.tm]
    simpa only [preliminaryNegLogOneSubRatio] using hTmRaw
  have hTa : B.ta.Contains
      (preliminaryNegLogOneSubRatio (preliminaryA r)) := by
    rw [CertifiedNumerics.negLogOneSubRatio_eq_of_ne hAPos.ne'] at hTaRaw
    rw [hvalid.ta]
    simpa only [preliminaryNegLogOneSubRatio] using hTaRaw
  have hOneMinusM : B.oneMinusM.Contains (1 - preliminaryM r) := by
    rw [hvalid.oneMinusM]
    simpa only [sub_eq_add_neg] using point_one.add hM.neg
  have hOneMinusMPos : 0 < B.oneMinusM.lo := by
    simpa only [positive, decide_eq_true_eq] using hsafe.oneMinusMPos
  have hInvOneMinusM :
      B.invOneMinusM.Contains ((1 - preliminaryM r)⁻¹) := by
    rw [hvalid.invOneMinusM]
    exact hOneMinusM.inv hOneMinusMPos
  have hULeft : B.uLeft.Contains
      (preliminaryMRatio r *
        preliminaryNegLogOneSubRatio (preliminaryM r)) := by
    rw [hvalid.uLeft]
    exact hMRatio.mulNonneg hTm hMR0 hTm0
  have hURight0 : B.uRight0.Contains
      (preliminaryARatio r *
        preliminaryNegLogOneSubRatio (preliminaryA r)) := by
    rw [hvalid.uRight0]
    exact hARatio.mulNonneg hTa hARatio0 hTa0
  have hURight : B.uRight.Contains
      (preliminaryARatio r * preliminaryNegLogOneSubRatio (preliminaryA r) *
        (1 - preliminaryM r)⁻¹) := by
    rw [hvalid.uRight]
    exact hURight0.mulNonneg hInvOneMinusM hURight00 hInvM0
  rw [hvalid.u]
  simpa only [preliminaryU, div_eq_mul_inv, mul_assoc] using hULeft.add hURight

set_option maxHeartbeats 0 in
theorem rest_contains {I : Interval} {B : Data} {r : ℝ}
    (hvalid : RestValid I B) (hsafe : RestSafety B)
    (hrI : I.Contains r) (hr : r ∈ Ioc (0 : ℝ) 1) :
    B.rest.Contains
      (preliminaryNormalizedSlack r - (1 + r) * Real.log (1 + r) / r) := by
  have hR0 : 0 ≤ B.r.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.rNonneg
  have hU0 : 0 ≤ B.u.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.uNonneg
  have hEv0 : 0 ≤ B.ev.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.evNonneg
  have hR : B.r.Contains r := by rw [hvalid.r]; exact hrI
  have hR2 : B.r2.Contains (r ^ 2) := by
    rw [hvalid.r2, pow_two]
    exact hR.mulNonneg hR hR0 hR0
  have hNegR : B.negR.Contains (-r) := by
    rw [hvalid.negR]
    exact hR.neg
  have hExpNegR : B.expNegR.Contains (Real.exp (-r)) := by
    rw [hvalid.expNegR]
    exact Sound.contains_exp_of_safe hNegR hsafe.negRExp
  have hU : B.u.Contains (preliminaryU r) :=
    u_contains hvalid hsafe hrI hr
  have hUPos := preliminaryU_pos hr
  have hV : B.v.Contains (r * preliminaryU r) := by
    rw [hvalid.v]
    exact hR.mulNonneg hU hR0 hU0
  have hEvRaw := Sound.contains_e_of_safe hV hsafe.vE
  have hEv : B.ev.Contains
      (preliminaryOneSubExpNegRatio (r * preliminaryU r)) := by
    rw [CertifiedNumerics.oneSubExpNegRatio_eq_of_ne
      (mul_ne_zero hr.1.ne' hUPos.ne')] at hEvRaw
    rw [hvalid.ev]
    simpa only [preliminaryOneSubExpNegRatio] using hEvRaw
  have hZ : B.z.Contains (preliminaryZ r) := by
    rw [hvalid.z]
    simpa only [preliminaryZ] using hU.mulNonneg hEv hU0 hEv0
  have hLogZ : B.logZ.Contains (Real.log (preliminaryZ r)) := by
    rw [hvalid.logZ]
    exact Sound.contains_log_of_safe hZ hsafe.zLog
  have hNegQuarter : (point (-(scale / 4))).Contains (-(1 / 4 : ℝ)) := by
    convert point_value (-(scale / 4)) using 1 <;> norm_num [value, scale]
  have hThreeForty : (point (3 * scale / 40)).Contains (3 / 40 : ℝ) := by
    convert point_value (3 * scale / 40) using 1 <;> norm_num [value, scale]
  have hTwoTwentyFive :
      (point (2 * scale / 25)).Contains (2 / 25 : ℝ) := by
    convert point_value (2 * scale / 25) using 1 <;> norm_num [value, scale]
  have hCorrection : B.correction.Contains
      (-(1 / 4 : ℝ) + (3 / 40 : ℝ) * r + (2 / 25 : ℝ) * r ^ 2) := by
    rw [hvalid.correction]
    convert (hNegQuarter.add (hThreeForty.mul hR)).add
      (hTwoTwentyFive.mul hR2) using 1 <;> ring
  have hNegHalf : (point (-(scale / 2))).Contains (-(1 / 2 : ℝ)) := by
    convert point_value (-(scale / 2)) using 1 <;> norm_num [value, scale]
  have hNegNineTwenty :
      (point (-(9 * scale / 20))).Contains (-(9 / 20 : ℝ)) := by
    convert point_value (-(9 * scale / 20)) using 1 <;> norm_num [value, scale]
  have hNegOneForty :
      (point (-(scale / 40))).Contains (-(1 / 40 : ℝ)) := by
    convert point_value (-(scale / 40)) using 1 <;> norm_num [value, scale]
  have hHalf : (point (scale / 2)).Contains (1 / 2 : ℝ) := by
    convert point_value (scale / 2) using 1 <;> norm_num [value, scale]
  rw [hvalid.rest]
  convert ((((hExpNegR.mul hCorrection).add (hNegHalf.mul hU)).add
    (hNegNineTwenty.mul hR)).add (hNegOneForty.mul hR2)).add
    (hHalf.mul hLogZ) using 1
  dsimp [preliminaryNormalizedSlack]
  field_simp [hr.1.ne']
  ring

set_option maxHeartbeats 0 in
theorem entropy_contains {I : Interval} {H : EntropyData}
    (hvalid : EntropyValid I H) (hsafe : EntropySafety H) :
    H.bound.Contains
      ((1 + value I.lo) / value I.lo * Real.log (1 + value I.lo)) := by
  have hAPos : 0 < H.a.lo := by
    simpa only [positive, decide_eq_true_eq] using hsafe.aPos
  have hOnePlusAPos : 0 < H.onePlusA.lo := by
    simpa only [positive, decide_eq_true_eq] using hsafe.onePlusAPos
  have hInvA0 : 0 ≤ H.invA.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.invANonneg
  have hFactor0 : 0 ≤ H.factor.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.factorNonneg
  have hLogA0 : 0 ≤ H.logA.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hsafe.logANonneg
  have hA : H.a.Contains (value I.lo) := by
    rw [hvalid.a]
    exact Interval.contains_point I.lo
  have hOnePlusA : H.onePlusA.Contains (1 + value I.lo) := by
    rw [hvalid.onePlusA]
    exact point_one.add hA
  have hInvA : H.invA.Contains (value I.lo)⁻¹ := by
    rw [hvalid.invA]
    exact hA.inv hAPos
  have hFactor : H.factor.Contains ((1 + value I.lo) / value I.lo) := by
    rw [hvalid.factor]
    simpa only [div_eq_mul_inv] using
      hOnePlusA.mulNonneg hInvA hOnePlusAPos.le hInvA0
  have hLogA : H.logA.Contains (Real.log (1 + value I.lo)) := by
    rw [hvalid.logA]
    exact Sound.contains_log_of_safe hOnePlusA hsafe.onePlusALog
  rw [hvalid.bound]
  exact hFactor.mulNonneg hLogA hFactor0 hLogA0

private def entropyRatio (r : ℝ) : ℝ :=
  (1 + r) * Real.log (1 + r) / r

private theorem hasDerivAt_entropyRatio {r : ℝ} (hr : 0 < r) :
    HasDerivAt entropyRatio ((r - Real.log (1 + r)) / r ^ 2) r := by
  have hOne : HasDerivAt (fun x : ℝ => 1 + x) 1 r :=
    (hasDerivAt_id r).const_add 1
  have hLog := hOne.log (by linarith : 1 + r ≠ 0)
  have hNum := hOne.mul hLog
  have h := hNum.div (hasDerivAt_id r) hr.ne'
  unfold entropyRatio
  convert h using 1 <;> try rfl
  field_simp [hr.ne', (by linarith : 1 + r ≠ 0)]
  simp only [id_eq, Pi.mul_apply]
  ring

private theorem strictMonoOn_entropyRatio :
    StrictMonoOn entropyRatio (Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
  · intro r hr
    exact (hasDerivAt_entropyRatio hr).continuousAt.continuousWithinAt
  · intro r hr
    have hrpos : 0 < r := by simpa using (interior_subset hr)
    rw [(hasDerivAt_entropyRatio hrpos).deriv]
    have hlog := Real.log_lt_sub_one_of_pos
      (by linarith : 0 < 1 + r) (by linarith : 1 + r ≠ 1)
    exact div_pos (by linarith) (sq_pos_of_pos hrpos)

set_option maxHeartbeats 0 in
theorem normalized_pos_of_positive_facts {I : Interval} {row : Row} {r : ℝ}
    (hfacts : PositiveFacts I row) (hrI : I.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hlo : 0 < value I.lo) :
    0 < preliminaryNormalizedSlack r := by
  have hRest := rest_contains hfacts.restValid
    (RestSafety.of_check hfacts.restSafe) hrI hr
  have hEntropy := entropy_contains hfacts.entropyValid
    (EntropySafety.of_check hfacts.entropySafe)
  have hLowerCheck :
      checkLowerEq (add row.entropy.bound row.common.rest) 1 = true := by
    simp only [checkLowerEq, add, decide_eq_true_eq]
    exact hfacts.lower
  have hSum := value_le_of_checkLowerEq hLowerCheck (hEntropy.add hRest)
  have hMono : entropyRatio (value I.lo) ≤ entropyRatio r :=
    strictMonoOn_entropyRatio.monotoneOn hlo hr.1 hrI.1
  have hEntropyEq :
      (1 + value I.lo) / value I.lo * Real.log (1 + value I.lo) =
        entropyRatio (value I.lo) := by
    unfold entropyRatio
    field_simp [hlo.ne']
  have hValue : 0 < value 1 := by norm_num [value, scale]
  rw [hEntropyEq] at hSum
  have hRestEq :
      (1 + r) * Real.log (1 + r) / r = entropyRatio r := rfl
  rw [hRestEq] at hSum
  exact hValue.trans_le (by linarith)

set_option maxHeartbeats 0 in
theorem full_contains {I : Interval} {B : Data} {r : ℝ}
    (hvalid : FullValid I B) (hrestSafe : RestSafety B)
    (hqSafe : qtSafe 12 B.r = true) (hOnePlusR0 : nonneg B.onePlusR = true)
    (hQr0 : nonneg B.qr = true) (hrI : I.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    B.full.Contains (preliminaryNormalizedSlack r) := by
  have hR : B.r.Contains r := by rw [hvalid.restValid.r]; exact hrI
  have hRest := rest_contains hvalid.restValid hrestSafe hrI hr
  have hQRaw := Sound.contains_q_of_safe hR hqSafe
  have hQ : B.qr.Contains (Real.log (1 + r) / r) := by
    rw [CertifiedNumerics.logOnePlusRatio_eq_of_ne hr.1.ne'] at hQRaw
    rw [hvalid.qr]
    exact hQRaw
  have hOnePlus : B.onePlusR.Contains (1 + r) := by
    rw [hvalid.restValid.onePlusR]
    exact point_one.add hR
  have hOnePlus0 : 0 ≤ B.onePlusR.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hOnePlusR0
  have hQ0 : 0 ≤ B.qr.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hQr0
  have hEntropy :
      B.entropy.Contains ((1 + r) * (Real.log (1 + r) / r)) := by
    rw [hvalid.entropy]
    exact hOnePlus.mulNonneg hQ hOnePlus0 hQ0
  rw [hvalid.full]
  convert hEntropy.add hRest using 1 <;> ring

set_option maxHeartbeats 0 in
theorem normalized_pos_of_origin_facts {I : Interval} {B : Data} {r : ℝ}
    (hfacts : OriginFacts I B) (hrI : I.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryNormalizedSlack r := by
  have hContains := full_contains hfacts.fullValid
    (RestSafety.of_check hfacts.restSafe) hfacts.qSafe
    hfacts.onePlusRNonneg hfacts.qrNonneg hrI hr
  have hLowerCheck : checkLowerEq B.full 1 = true := by
    simp only [checkLowerEq, decide_eq_true_eq]
    exact hfacts.lower
  have hLower := value_le_of_checkLowerEq hLowerCheck hContains
  have hValue : 0 < value 1 := by norm_num [value, scale]
  exact hValue.trans_le hLower

end

end RamseyLean.PreliminaryCertificate


