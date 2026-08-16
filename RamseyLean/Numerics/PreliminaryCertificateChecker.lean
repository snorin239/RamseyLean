import RamseyLean.Analysis.FixedPointInterval

/-!
# Linear fixed-point checker for the preliminary numerical certificate

The preliminary case of paper Lemma `lem:numerics` uses a cached row for every
mesh cell. Each transition checks only one node of the numerical DAG against
its immediate predecessors, preventing repeated kernel expansion.
-/

set_option autoImplicit false

namespace RamseyLean.PreliminaryCertificate

open FixedPointInterval

structure Data where
  r : Interval
  r2 : Interval
  r3 : Interval
  onePlusR : Interval
  remainder : Interval
  negR : Interval
  expNegR : Interval
  mExponent : Interval
  mRatio : Interval
  m : Interval
  aInner : Interval
  aExp : Interval
  invOnePlusR : Interval
  aRatio : Interval
  a : Interval
  tm : Interval
  ta : Interval
  oneMinusM : Interval
  invOneMinusM : Interval
  uLeft : Interval
  uRight0 : Interval
  uRight : Interval
  u : Interval
  v : Interval
  ev : Interval
  z : Interval
  logZ : Interval
  correction : Interval
  rest : Interval
  qr : Interval
  entropy : Interval
  full : Interval
deriving Repr

structure EntropyData where
  a : Interval
  onePlusA : Interval
  invA : Interval
  factor : Interval
  logA : Interval
  bound : Interval
deriving Repr

structure Row where
  common : Data
  entropy : EntropyData
deriving Repr

def intervalEq (I J : Interval) : Bool := decide (I = J)

def restTransitions (I : Interval) (B : Data) : Bool :=
  intervalEq B.r I &&
  intervalEq B.r2 (mulNonneg B.r B.r) &&
  intervalEq B.r3 (mulNonneg B.r2 B.r) &&
  intervalEq B.onePlusR (add (point scale) B.r) &&
  intervalEq B.remainder
    (add (add (add (point (-(scale / 4)))
      (mul (point (2 * scale / 5)) B.r))
      (mul (point (33 * scale / 200)) B.r2))
      (mul (point (-(2 * scale / 25))) B.r3)) &&
  intervalEq B.negR (neg B.r) &&
  intervalEq B.expNegR (exp 10 B.negR) &&
  intervalEq B.mExponent
    (add (mul (point (-(9 * scale / 10))) B.r)
      (mul (point (-(scale / 20))) B.r2)) &&
  intervalEq B.mRatio (exp 10 B.mExponent) &&
  intervalEq B.m (mulNonneg B.r B.mRatio) &&
  intervalEq B.aInner (neg (mul B.expNegR B.remainder)) &&
  intervalEq B.aExp (exp 10 B.aInner) &&
  intervalEq B.invOnePlusR (inv B.onePlusR) &&
  intervalEq B.aRatio (mulNonneg B.aExp B.invOnePlusR) &&
  intervalEq B.a (mulNonneg B.r B.aRatio) &&
  intervalEq B.tm (t 12 B.m) &&
  intervalEq B.ta (t 12 B.a) &&
  intervalEq B.oneMinusM (add (point scale) (neg B.m)) &&
  intervalEq B.invOneMinusM (inv B.oneMinusM) &&
  intervalEq B.uLeft (mulNonneg B.mRatio B.tm) &&
  intervalEq B.uRight0 (mulNonneg B.aRatio B.ta) &&
  intervalEq B.uRight (mulNonneg B.uRight0 B.invOneMinusM) &&
  intervalEq B.u (add B.uLeft B.uRight) &&
  intervalEq B.v (mulNonneg B.r B.u) &&
  intervalEq B.ev (e 10 B.v) &&
  intervalEq B.z (mulNonneg B.u B.ev) &&
  intervalEq B.logZ (log 10 B.z) &&
  intervalEq B.correction
    (add (add (point (-(scale / 4)))
      (mul (point (3 * scale / 40)) B.r))
      (mul (point (2 * scale / 25)) B.r2)) &&
  intervalEq B.rest
    (add (add (add (add
      (mul B.expNegR B.correction)
      (mul (point (-(scale / 2))) B.u))
      (mul (point (-(9 * scale / 20))) B.r))
      (mul (point (-(scale / 40))) B.r2))
      (mul (point (scale / 2)) B.logZ))

def restSafe (B : Data) : Bool :=
  nonneg B.r && nonneg B.r2 && expSafe 10 B.negR &&
  expSafe 10 B.mExponent && nonneg B.mRatio && nonneg B.m &&
  expSafe 10 B.aInner && positive B.onePlusR && nonneg B.aExp &&
  nonneg B.invOnePlusR && nonneg B.aRatio && nonneg B.a &&
  qtSafe 12 B.m && qtSafe 12 B.a && nonneg B.tm && nonneg B.ta &&
  positive B.oneMinusM && nonneg B.invOneMinusM &&
  nonneg B.uLeft && nonneg B.uRight0 && nonneg B.uRight && nonneg B.u &&
  eSafe 10 B.v && nonneg B.ev && nonneg B.z && positive B.z &&
  logSafe 10 B.z

def entropyTransitions (I : Interval) (H : EntropyData) : Bool :=
  intervalEq H.a (point I.lo) &&
  intervalEq H.onePlusA (add (point scale) H.a) &&
  intervalEq H.invA (inv H.a) &&
  intervalEq H.factor (mulNonneg H.onePlusA H.invA) &&
  intervalEq H.logA (log 10 H.onePlusA) &&
  intervalEq H.bound (mulNonneg H.factor H.logA)

def entropySafe (H : EntropyData) : Bool :=
  positive H.a && positive H.onePlusA && nonneg H.invA &&
  nonneg H.factor && logSafe 10 H.onePlusA && nonneg H.logA

def checkPositive (I : Interval) (row : Row) : Bool :=
  restTransitions I row.common &&
    (restSafe row.common &&
      (entropyTransitions I row.entropy &&
        (entropySafe row.entropy &&
          decide (1 ≤ row.entropy.bound.lo + row.common.rest.lo))))

def fullTransitions (I : Interval) (B : Data) : Bool :=
  restTransitions I B &&
  intervalEq B.qr (q 12 B.r) &&
  intervalEq B.entropy (mulNonneg B.onePlusR B.qr) &&
  intervalEq B.full (add B.entropy B.rest)

def fullSafe (B : Data) : Bool :=
  restSafe B && qtSafe 12 B.r && nonneg B.onePlusR && nonneg B.qr

def checkOrigin (I : Interval) (B : Data) : Bool :=
  fullTransitions I B && fullSafe B && decide (1 ≤ B.full.lo)

structure RestValid (I : Interval) (B : Data) : Prop where
  r : B.r = I
  r2 : B.r2 = mulNonneg B.r B.r
  r3 : B.r3 = mulNonneg B.r2 B.r
  onePlusR : B.onePlusR = add (point scale) B.r
  remainder : B.remainder =
    add (add (add (point (-(scale / 4)))
      (mul (point (2 * scale / 5)) B.r))
      (mul (point (33 * scale / 200)) B.r2))
      (mul (point (-(2 * scale / 25))) B.r3)
  negR : B.negR = neg B.r
  expNegR : B.expNegR = exp 10 B.negR
  mExponent : B.mExponent = add
    (mul (point (-(9 * scale / 10))) B.r)
    (mul (point (-(scale / 20))) B.r2)
  mRatio : B.mRatio = exp 10 B.mExponent
  m : B.m = mulNonneg B.r B.mRatio
  aInner : B.aInner = neg (mul B.expNegR B.remainder)
  aExp : B.aExp = exp 10 B.aInner
  invOnePlusR : B.invOnePlusR = inv B.onePlusR
  aRatio : B.aRatio = mulNonneg B.aExp B.invOnePlusR
  a : B.a = mulNonneg B.r B.aRatio
  tm : B.tm = t 12 B.m
  ta : B.ta = t 12 B.a
  oneMinusM : B.oneMinusM = add (point scale) (neg B.m)
  invOneMinusM : B.invOneMinusM = inv B.oneMinusM
  uLeft : B.uLeft = mulNonneg B.mRatio B.tm
  uRight0 : B.uRight0 = mulNonneg B.aRatio B.ta
  uRight : B.uRight = mulNonneg B.uRight0 B.invOneMinusM
  u : B.u = add B.uLeft B.uRight
  v : B.v = mulNonneg B.r B.u
  ev : B.ev = e 10 B.v
  z : B.z = mulNonneg B.u B.ev
  logZ : B.logZ = log 10 B.z
  correction : B.correction =
    add (add (point (-(scale / 4)))
      (mul (point (3 * scale / 40)) B.r))
      (mul (point (2 * scale / 25)) B.r2)
  rest : B.rest = add (add (add (add
    (mul B.expNegR B.correction)
    (mul (point (-(scale / 2))) B.u))
    (mul (point (-(9 * scale / 20))) B.r))
    (mul (point (-(scale / 40))) B.r2))
    (mul (point (scale / 2)) B.logZ)

theorem RestValid.of_check {I : Interval} {B : Data}
    (h : restTransitions I B = true) : RestValid I B := by
  constructor <;>
    simp_all only [restTransitions, intervalEq, Bool.and_eq_true,
      decide_eq_true_eq]

structure EntropyValid (I : Interval) (H : EntropyData) : Prop where
  a : H.a = point I.lo
  onePlusA : H.onePlusA = add (point scale) H.a
  invA : H.invA = inv H.a
  factor : H.factor = mulNonneg H.onePlusA H.invA
  logA : H.logA = log 10 H.onePlusA
  bound : H.bound = mulNonneg H.factor H.logA

theorem EntropyValid.of_check {I : Interval} {H : EntropyData}
    (h : entropyTransitions I H = true) : EntropyValid I H := by
  constructor <;>
    simp_all only [entropyTransitions, intervalEq, Bool.and_eq_true,
      decide_eq_true_eq]

structure PositiveFacts (I : Interval) (row : Row) : Prop where
  restValid : RestValid I row.common
  restSafe : PreliminaryCertificate.restSafe row.common = true
  entropyValid : EntropyValid I row.entropy
  entropySafe : PreliminaryCertificate.entropySafe row.entropy = true
  lower : 1 ≤ row.entropy.bound.lo + row.common.rest.lo

theorem PositiveFacts.of_check {I : Interval} {row : Row}
    (h : checkPositive I row = true) : PositiveFacts I row := by
  have hp : restTransitions I row.common = true ∧
      PreliminaryCertificate.restSafe row.common = true ∧
      entropyTransitions I row.entropy = true ∧
      PreliminaryCertificate.entropySafe row.entropy = true ∧
      decide (1 ≤ row.entropy.bound.lo + row.common.rest.lo) = true := by
    simpa only [checkPositive, Bool.and_eq_true] using h
  exact ⟨RestValid.of_check hp.1, hp.2.1,
    EntropyValid.of_check hp.2.2.1, hp.2.2.2.1,
    by simpa only [decide_eq_true_eq] using hp.2.2.2.2⟩

structure FullValid (I : Interval) (B : Data) : Prop where
  restValid : RestValid I B
  qr : B.qr = q 12 B.r
  entropy : B.entropy = mulNonneg B.onePlusR B.qr
  full : B.full = add B.entropy B.rest

theorem FullValid.of_check {I : Interval} {B : Data}
    (h : fullTransitions I B = true) : FullValid I B := by
  have hp : ((restTransitions I B = true ∧
      intervalEq B.qr (q 12 B.r) = true) ∧
      intervalEq B.entropy (mulNonneg B.onePlusR B.qr) = true) ∧
      intervalEq B.full (add B.entropy B.rest) = true := by
    simpa only [fullTransitions, Bool.and_eq_true] using h
  exact ⟨RestValid.of_check hp.1.1.1,
    by simpa only [intervalEq, decide_eq_true_eq] using hp.1.1.2,
    by simpa only [intervalEq, decide_eq_true_eq] using hp.1.2,
    by simpa only [intervalEq, decide_eq_true_eq] using hp.2⟩

structure OriginFacts (I : Interval) (B : Data) : Prop where
  fullValid : FullValid I B
  restSafe : PreliminaryCertificate.restSafe B = true
  qSafe : qtSafe 12 B.r = true
  onePlusRNonneg : nonneg B.onePlusR = true
  qrNonneg : nonneg B.qr = true
  lower : 1 ≤ B.full.lo

theorem OriginFacts.of_check {I : Interval} {B : Data}
    (h : checkOrigin I B = true) : OriginFacts I B := by
  have hp : (fullTransitions I B = true ∧
      (((PreliminaryCertificate.restSafe B = true ∧ qtSafe 12 B.r = true) ∧
        nonneg B.onePlusR = true) ∧ nonneg B.qr = true)) ∧
      decide (1 ≤ B.full.lo) = true := by
    simpa only [checkOrigin, fullSafe, Bool.and_eq_true] using h
  exact ⟨FullValid.of_check hp.1.1, hp.1.2.1.1.1, hp.1.2.1.1.2,
    hp.1.2.1.2, hp.1.2.2,
    by simpa only [decide_eq_true_eq] using hp.2⟩

end RamseyLean.PreliminaryCertificate
