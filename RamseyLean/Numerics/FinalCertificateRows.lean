import RamseyLean.Numerics.FinalCertificateBranches
import RamseyLean.Analysis.UniformMesh

/-!
# Literal-row certificates for the final numerical descent

Generated certificate rows contain claimed fixed-point endpoints.  The checks
in this module validate one local DAG transition at a time; their soundness is
then obtained from the named branch analyzers without re-evaluating the whole
expression during theorem proving.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

deriving instance DecidableEq for CommonData

def intervalEq (I J : Interval) : Bool := decide (I = J)
def recordEq {α : Type} [DecidableEq α] (x y : α) : Bool := decide (x = y)

theorem intervalEq_eq_true {I J : Interval} (h : intervalEq I J = true) : I = J := by
  simpa only [intervalEq, decide_eq_true_eq] using h

def commonTransitions : CommonData → Bool
  | { input, r2, r3, remainder, negR, expNegR, mExponent, mRatio, m,
      aInner, aExp, onePlusR, invOnePlusR, aRatio, a, tm, ta, oneMinusM,
      invOneMinusM, uLeft, uRight0, uRight, u } =>
    intervalEq r2 (mulNonneg input input) &&
    intervalEq r3 (mulNonneg r2 input) &&
    intervalEq remainder
      (add (add (add (rationalInterval (-1) 4)
        (mul (rationalInterval 31 100) input))
        (mul (rationalInterval 21 100) r2))
        (mul (rationalInterval (-2) 25) r3)) &&
    intervalEq negR (neg input) && intervalEq expNegR (exp 12 negR) &&
    intervalEq mExponent (add (mul (rationalInterval (-7) 10) input)
      (mul (rationalInterval (-13) 50) r2)) &&
    intervalEq mRatio (exp 12 mExponent) &&
    intervalEq m (mulNonneg input mRatio) &&
    intervalEq aInner (neg (mul expNegR remainder)) &&
    intervalEq aExp (exp 12 aInner) &&
    intervalEq onePlusR (add (point scale) input) &&
    intervalEq invOnePlusR (inv onePlusR) &&
    intervalEq aRatio (mulNonneg aExp invOnePlusR) &&
    intervalEq a (mulNonneg input aRatio) && intervalEq tm (t 16 m) &&
    intervalEq ta (t 16 a) &&
    intervalEq oneMinusM (sub (point scale) m) &&
    intervalEq invOneMinusM (inv oneMinusM) &&
    intervalEq uLeft (mulNonneg mRatio tm) &&
    intervalEq uRight0 (mulNonneg aRatio ta) &&
    intervalEq uRight (mulNonneg uRight0 invOneMinusM) &&
    intervalEq u (add uLeft uRight)

theorem CommonData.wellFormed_of_transitions {d : CommonData}
    (h : commonTransitions d = true) : d.WellFormed := by
  cases d
  simp only [commonTransitions, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  constructor <;> aesop

def smallTransitions : SmallData → Bool
  | { input, band, common, ratio, parameter, negT, expNegT, onePlusR, qr,
      entropy, corr, tail, base, onePlusT, logRatio, logOnePlusT, expR,
      logAWithoutR, slack, logB, coordinateGap } =>
    recordEq common (commonData input) &&
    intervalEq ratio (smallRatio band input) &&
    intervalEq parameter (mulNonneg input ratio) &&
    intervalEq negT (neg parameter) && intervalEq expNegT (exp 12 negT) &&
    intervalEq onePlusR (add (point scale) input) &&
    intervalEq qr (q 16 input) &&
    intervalEq entropy (mulNonneg onePlusR qr) &&
    intervalEq corr (correction input common.r2 common.expNegR) &&
    intervalEq tail (commonTail input common.r2 common.u) &&
    intervalEq base (add (add entropy corr) tail) &&
    intervalEq onePlusT (add (point scale) parameter) &&
    intervalEq logRatio (log 16 ratio) &&
    intervalEq logOnePlusT (log 16 onePlusT) &&
    intervalEq expR (mul expNegT (preliminaryR parameter)) &&
    intervalEq logAWithoutR (sub (sub logRatio logOnePlusT) expR) &&
    intervalEq slack (add base (divNat logAWithoutR 2)) &&
    intervalEq logB (add (neg logOnePlusT)
      (mul expNegT (preliminaryS parameter))) &&
    intervalEq coordinateGap (add (mulNonneg input common.u) logB)

theorem SmallData.wellFormed_of_transitions {d : SmallData}
    (h : smallTransitions d = true) : d.WellFormed := by
  rcases d with ⟨input, band, common, ratio, parameter, negT, expNegT,
    onePlusR, qr, entropy, corr, tail, base, onePlusT, logRatio,
    logOnePlusT, expR, logAWithoutR, slack, logB, coordinateGap⟩
  simp only [smallTransitions, intervalEq, recordEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  constructor <;> aesop

def smallCoordinateTransitions : SmallCoordinateData → Bool
  | { small, parameter2, qt, ratioQt, ratio2, rRatio2, factor, expFactor,
      positiveTerm, normalizedGap } =>
    smallTransitions small &&
    intervalEq parameter2 (mulNonneg small.parameter small.parameter) &&
    intervalEq qt (q 16 small.parameter) &&
    intervalEq ratioQt (mulNonneg small.ratio qt) &&
    intervalEq ratio2 (mulNonneg small.ratio small.ratio) &&
    intervalEq rRatio2 (mulNonneg small.input ratio2) &&
    intervalEq factor (add (add (rationalInterval 13 40)
      (mul (rationalInterval 17 200) small.parameter))
      (mul (rationalInterval (-2) 25) parameter2)) &&
    intervalEq expFactor (mul small.expNegT factor) &&
    intervalEq positiveTerm (mul rRatio2 expFactor) &&
    intervalEq normalizedGap (add (sub small.common.u ratioQt) positiveTerm)

theorem SmallCoordinateData.wellFormed_of_transitions
    {d : SmallCoordinateData} (h : smallCoordinateTransitions d = true) :
    d.WellFormed := by
  rcases d with ⟨small, parameter2, qt, ratioQt, ratio2, rRatio2, factor,
    expFactor, positiveTerm, normalizedGap⟩
  simp only [smallCoordinateTransitions, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  constructor
  · exact SmallData.wellFormed_of_transitions h.1.1.1.1.1.1.1.1.1
  all_goals aesop

def smallCoordinateQuotientTransitions : SmallCoordinateQuotientData → Bool
  | { small, parameter2, invParameter, qt, ratioQt, ratio2, rRatio2, factor,
      expFactor, positiveTerm, normalizedGap } =>
    smallTransitions small &&
    intervalEq parameter2 (mulNonneg small.parameter small.parameter) &&
    intervalEq invParameter (inv small.parameter) &&
    intervalEq qt (mulNonneg small.logOnePlusT invParameter) &&
    intervalEq ratioQt (mulNonneg small.ratio qt) &&
    intervalEq ratio2 (mulNonneg small.ratio small.ratio) &&
    intervalEq rRatio2 (mulNonneg small.input ratio2) &&
    intervalEq factor (add (add (rationalInterval 13 40)
      (mul (rationalInterval 17 200) small.parameter))
      (mul (rationalInterval (-2) 25) parameter2)) &&
    intervalEq expFactor (mul small.expNegT factor) &&
    intervalEq positiveTerm (mul rRatio2 expFactor) &&
    intervalEq normalizedGap (add (sub small.common.u ratioQt) positiveTerm)

theorem SmallCoordinateQuotientData.wellFormed_of_transitions
    {d : SmallCoordinateQuotientData}
    (h : smallCoordinateQuotientTransitions d = true) : d.WellFormed := by
  rcases d with ⟨small, parameter2, invParameter, qt, ratioQt, ratio2,
    rRatio2, factor, expFactor, positiveTerm, normalizedGap⟩
  simp only [smallCoordinateQuotientTransitions, intervalEq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  constructor
  · exact SmallData.wellFormed_of_transitions h.1.1.1.1.1.1.1.1.1.1
  all_goals aesop

def smallCoordinateCheck (d : SmallCoordinateData) : Bool :=
  smallCoordinateTransitions d && d.safe && checkLower d.small.slack 0 &&
    checkLower d.normalizedGap 0

def smallCoordinateQuotientCheck (d : SmallCoordinateQuotientData) : Bool :=
  smallCoordinateQuotientTransitions d && d.safe &&
    checkLower d.small.slack 0 && checkLower d.normalizedGap 0

structure SmallRowFacts (d : SmallCoordinateData) : Prop where
  wellFormed : d.WellFormed
  checks : d.Checks
  slackPositive : checkLower d.small.slack 0 = true
  coordinatePositive : checkLower d.normalizedGap 0 = true

theorem smallRowFacts_of_check {d : SmallCoordinateData}
    (h : smallCoordinateCheck d = true) : SmallRowFacts d := by
  simp only [smallCoordinateCheck, Bool.and_eq_true] at h
  exact ⟨SmallCoordinateData.wellFormed_of_transitions h.1.1.1,
    SmallCoordinateData.checks_of_safe h.1.1.2, h.1.2, h.2⟩

structure SmallQuotientRowFacts (d : SmallCoordinateQuotientData) : Prop where
  wellFormed : d.WellFormed
  checks : d.Checks
  slackPositive : checkLower d.small.slack 0 = true
  coordinatePositive : checkLower d.normalizedGap 0 = true

theorem smallQuotientRowFacts_of_check {d : SmallCoordinateQuotientData}
    (h : smallCoordinateQuotientCheck d = true) : SmallQuotientRowFacts d := by
  simp only [smallCoordinateQuotientCheck, Bool.and_eq_true] at h
  exact ⟨SmallCoordinateQuotientData.wellFormed_of_transitions h.1.1.1,
    SmallCoordinateQuotientData.checks_of_safe h.1.1.2, h.1.2, h.2⟩

end

end RamseyLean.FinalCertificate







