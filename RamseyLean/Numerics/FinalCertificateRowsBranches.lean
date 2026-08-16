import RamseyLean.Numerics.FinalCertificateRows

/-! Literal-row validators for the middle, cap, large, and crossing branches. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

deriving instance DecidableEq for EntropyData
deriving instance DecidableEq for FOneData

def middleTransitions : MiddleData → Bool
  | { input, common, entropy, fOne, oneMinusR, uTerm, tail, corr,
      logTerm, fOneTerm, slack } =>
    recordEq common (commonData input) &&
    recordEq entropy (entropyData input) && recordEq fOne fOneData &&
    intervalEq oneMinusR (sub (point scale) input) &&
    intervalEq uTerm (neg (divNat (mul oneMinusR common.u) 2)) &&
    intervalEq tail (add (add uTerm (mul (rationalInterval (-7) 20) input))
      (mul (rationalInterval (-13) 100) common.r2)) &&
    intervalEq corr (correction input common.r2 common.expNegR) &&
    intervalEq logTerm (neg (divNat entropy.logInput 2)) &&
    intervalEq fOneTerm (neg (divNat fOne.value 2)) &&
    intervalEq slack (add (add (add (add entropy.entropy corr) tail)
      logTerm) fOneTerm)

theorem MiddleData.wellFormed_of_transitions {d : MiddleData}
    (h : middleTransitions d = true) : d.WellFormed := by
  rcases d with ⟨input, common, entropy, fOne, oneMinusR, uTerm, tail,
    corr, logTerm, fOneTerm, slack⟩
  simp only [middleTransitions, recordEq, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  constructor <;> aesop

def middleCheck (d : MiddleData) : Bool :=
  middleTransitions d && d.safe && checkLower d.slack 0

structure MiddleRowFacts (d : MiddleData) : Prop where
  wellFormed : d.WellFormed
  checks : d.Checks
  slackPositive : checkLower d.slack 0 = true

theorem middleRowFacts_of_check {d : MiddleData} (h : middleCheck d = true) :
    MiddleRowFacts d := by
  simp only [middleCheck, Bool.and_eq_true] at h
  exact ⟨MiddleData.wellFormed_of_transitions h.1.1,
    MiddleData.checks_of_safe h.1.2, h.2⟩

def largeTransitions : LargeData → Bool
  | { input, parameter, common, entropy, negT, expNegT, onePlusT,
      logT, logOnePlusT, expR, logA, logB, corr, tail, logTerm, base,
      slack, coordinateGap } =>
    recordEq common (commonData input) &&
    recordEq entropy (entropyData input) && intervalEq negT (neg parameter) &&
    intervalEq expNegT (exp 12 negT) &&
    intervalEq onePlusT (add (point scale) parameter) &&
    intervalEq logT (log 16 parameter) &&
    intervalEq logOnePlusT (log 16 onePlusT) &&
    intervalEq expR (mul expNegT (preliminaryR parameter)) &&
    intervalEq logA (sub (sub logT logOnePlusT) expR) &&
    intervalEq logB (add (neg logOnePlusT)
      (mul expNegT (preliminaryS parameter))) &&
    intervalEq corr (correction input common.r2 common.expNegR) &&
    intervalEq tail (commonTail input common.r2 common.u) &&
    intervalEq logTerm (neg (divNat entropy.logInput 2)) &&
    intervalEq base (add (add (add entropy.entropy corr) tail) logTerm) &&
    intervalEq slack (add base (divNat logB 2)) &&
    intervalEq coordinateGap (add (mulNonneg input common.u) logA)

theorem LargeData.wellFormed_of_transitions {d : LargeData}
    (h : largeTransitions d = true) : d.WellFormed := by
  rcases d with ⟨input, parameter, common, entropy, negT, expNegT,
    onePlusT, logT, logOnePlusT, expR, logA, logB, corr, tail, logTerm,
    base, slack, coordinateGap⟩
  simp only [largeTransitions, recordEq, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  constructor <;> aesop

def largeCheck (band : LargeBand) (d : LargeData) : Bool :=
  largeTransitions d && intervalEq d.parameter (largeParameter band d.input) &&
    d.safe && checkLower d.slack 0 && checkLower d.coordinateGap 0

def capCheck (d : LargeData) : Bool :=
  largeTransitions d && intervalEq d.parameter (point scale) && d.safe &&
    checkLower d.slack 0

structure LargeRowFacts (band : LargeBand) (d : LargeData) : Prop where
  wellFormed : d.WellFormed
  parameter : d.parameter = largeParameter band d.input
  checks : d.Checks
  slackPositive : checkLower d.slack 0 = true
  coordinatePositive : checkLower d.coordinateGap 0 = true

theorem largeRowFacts_of_check {band : LargeBand} {d : LargeData}
    (h : largeCheck band d = true) : LargeRowFacts band d := by
  simp only [largeCheck, Bool.and_eq_true, intervalEq, decide_eq_true_eq] at h
  exact ⟨LargeData.wellFormed_of_transitions h.1.1.1.1,
    h.1.1.1.2, LargeData.checks_of_safe h.1.1.2, h.1.2, h.2⟩

structure CapRowFacts (d : LargeData) : Prop where
  wellFormed : d.WellFormed
  parameter : d.parameter = point scale
  checks : d.Checks
  slackPositive : checkLower d.slack 0 = true

theorem capRowFacts_of_check {d : LargeData} (h : capCheck d = true) :
    CapRowFacts d := by
  simp only [capCheck, Bool.and_eq_true, intervalEq, decide_eq_true_eq] at h
  exact ⟨LargeData.wellFormed_of_transitions h.1.1.1,
    h.1.1.2, LargeData.checks_of_safe h.1.2, h.2⟩

def crossingTransitions : CrossingData → Bool
  | { input, common, parameter, negT, expNegT, onePlusT, logT,
      logOnePlusT, expR, logA, logB, rU, aGap, bGap } =>
    recordEq common (commonData input) && intervalEq parameter (point scale) &&
    intervalEq negT (neg parameter) && intervalEq expNegT (exp 12 negT) &&
    intervalEq onePlusT (add (point scale) parameter) &&
    intervalEq logT (log 16 parameter) &&
    intervalEq logOnePlusT (log 16 onePlusT) &&
    intervalEq expR (mul expNegT (preliminaryR parameter)) &&
    intervalEq logA (sub (sub logT logOnePlusT) expR) &&
    intervalEq logB (add (neg logOnePlusT)
      (mul expNegT (preliminaryS parameter))) &&
    intervalEq rU (mulNonneg input common.u) &&
    intervalEq aGap (add rU logA) && intervalEq bGap (add rU logB)

theorem CrossingData.wellFormed_of_transitions {d : CrossingData}
    (h : crossingTransitions d = true) : d.WellFormed := by
  rcases d with ⟨input, common, parameter, negT, expNegT, onePlusT,
    logT, logOnePlusT, expR, logA, logB, rU, aGap, bGap⟩
  simp only [crossingTransitions, recordEq, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  constructor <;> aesop

def crossingCheck (d : CrossingData) : Bool :=
  crossingTransitions d && d.safe &&
    (if d.input.hi ≤ 257800000000 then checkLower (neg d.bGap) 0 else true) &&
    (if 258000000000 ≤ d.input.lo then checkLowerEq d.bGap 0 else true) &&
    (if d.input.hi ≤ 360400000000 then checkLowerEq (neg d.aGap) 0 else true) &&
    (if 360500000000 ≤ d.input.lo then checkLower d.aGap 0 else true)

structure CrossingRowFacts (d : CrossingData) : Prop where
  wellFormed : d.WellFormed
  checks : d.Checks
  bBelow : d.input.hi ≤ 257800000000 → checkLower (neg d.bGap) 0 = true
  bAbove : 258000000000 ≤ d.input.lo → checkLowerEq d.bGap 0 = true
  aBelow : d.input.hi ≤ 360400000000 → checkLowerEq (neg d.aGap) 0 = true
  aAbove : 360500000000 ≤ d.input.lo → checkLower d.aGap 0 = true

theorem crossingRowFacts_of_check {d : CrossingData} (h : crossingCheck d = true) :
    CrossingRowFacts d := by
  simp only [crossingCheck, Bool.and_eq_true] at h
  refine ⟨CrossingData.wellFormed_of_transitions h.1.1.1.1.1,
    CrossingData.checks_of_safe h.1.1.1.1.2, ?_, ?_, ?_, ?_⟩
  · intro hb
    simp only [if_pos hb] at h
    exact h.1.1.1.2
  · intro hb
    simp only [if_pos hb] at h
    exact h.1.1.2
  · intro ha
    simp only [if_pos ha] at h
    exact h.1.2
  · intro ha
    simp only [if_pos ha] at h
    exact h.2

end

end RamseyLean.FinalCertificate
