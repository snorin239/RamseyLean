import RamseyLean.Numerics.Final
import RamseyLean.Analysis.FixedPointInterval

/-!
# Fixed-point certificates for the final numerical descent

This module evaluates the four one-variable branches exposed by
`RamseyLean.Numerics.Final` with the kernel-checked fixed-point interval
backend.  The analyzers retain the intermediate bounds needed for a staged
soundness proof and for fast `List.all` certificate reduction.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

/-- A rational singleton enlarged outwards to the fixed-point grid. -/
def rationalInterval (p : ℤ) (q : ℕ) : Interval :=
  divNat (point (p * scale)) q

def sub (I J : Interval) : Interval := add I (neg J)

def quartic (c₀ c₁ c₂ c₃ c₄ u : Interval) : Interval :=
  add c₀ (mul u (add c₁ (mul u (add c₂ (mul u (add c₃ (mul u c₄)))))))

inductive SmallBand
  | zeroTenth
  | tenthFifth
  | fifthCut
deriving DecidableEq, Repr

inductive LargeBand
  | cutNineTwentieths
  | nineTwentiethsThreeFifths
  | threeFifthsOne
deriving DecidableEq, Repr

/-- The selected quartic approximation to `t / r` on a small branch band. -/
def smallRatio (band : SmallBand) (r : Interval) : Interval :=
  match band with
  | .zeroTenth =>
      let u := mul (rationalInterval 10 1) r
      quartic (rationalInterval 22764 10000) (rationalInterval 4213 10000)
        (rationalInterval 823 10000) (rationalInterval 213 10000)
        (rationalInterval (-41) 10000) u
  | .tenthFifth =>
      let u := sub (mul (rationalInterval 10 1) r) (rationalInterval 1 1)
      quartic (rationalInterval 27971 10000) (rationalInterval 6328 10000)
        (rationalInterval 1148 10000) (rationalInterval 29 10000)
        (rationalInterval (-385) 10000) u
  | .fifthCut =>
      let u := mul (rationalInterval 50 3)
        (sub r (rationalInterval 1 5))
      quartic (rationalInterval 35092 10000) (rationalInterval 4307 10000)
        (rationalInterval (-348) 10000) (rationalInterval (-305) 10000)
        (rationalInterval 65 10000) u

/-- The selected quartic approximation to `t` on a raw large branch band. -/
def largeParameter (band : LargeBand) (r : Interval) : Interval :=
  match band with
  | .cutNineTwentieths =>
      let u := mul (rationalInterval 100 9)
        (sub r (rationalInterval 9 25))
      quartic (rationalInterval 10036 10000) (rationalInterval (-4315) 10000)
        (rationalInterval 1157 10000) (rationalInterval (-101) 10000)
        (rationalInterval (-23) 10000) u
  | .nineTwentiethsThreeFifths =>
      let u := mul (rationalInterval 20 3)
        (sub r (rationalInterval 9 20))
      quartic (rationalInterval 6755 10000) (rationalInterval (-3986) 10000)
        (rationalInterval 2018 10000) (rationalInterval (-717) 10000)
        (rationalInterval 136 10000) u
  | .threeFifthsOne =>
      let u := mul (rationalInterval 5 2)
        (sub r (rationalInterval 3 5))
      quartic (rationalInterval 4206 10000) (rationalInterval (-4085) 10000)
        (rationalInterval 4170 10000) (rationalInterval (-2475) 10000)
        (rationalInterval 702 10000) u

structure CommonResult where
  safe : Bool
  r2 : Interval
  expNegR : Interval
  mRatio : Interval
  m : Interval
  aRatio : Interval
  a : Interval
  u : Interval
deriving Repr

/-- Staged enclosure of `finalU` and its shared elementary subexpressions. -/
def common (r : Interval) : CommonResult :=
  let r2 := mulNonneg r r
  let r3 := mulNonneg r2 r
  let remainder :=
    add (add (add (rationalInterval (-1) 4)
      (mul (rationalInterval 31 100) r))
      (mul (rationalInterval 21 100) r2))
      (mul (rationalInterval (-2) 25) r3)
  let negR := neg r
  let expNegR := exp 12 negR
  let mExponent := add (mul (rationalInterval (-7) 10) r)
    (mul (rationalInterval (-13) 50) r2)
  let mRatio := exp 12 mExponent
  let m := mulNonneg r mRatio
  let aInner := neg (mul expNegR remainder)
  let aExp := exp 12 aInner
  let onePlusR := add (point scale) r
  let invOnePlusR := inv onePlusR
  let aRatio := mulNonneg aExp invOnePlusR
  let a := mulNonneg r aRatio
  let tm := t 16 m
  let ta := t 16 a
  let oneMinusM := sub (point scale) m
  let invOneMinusM := inv oneMinusM
  let uLeft := mulNonneg mRatio tm
  let uRight0 := mulNonneg aRatio ta
  let uRight := mulNonneg uRight0 invOneMinusM
  let u := add uLeft uRight
  let safe :=
    nonneg r && nonneg r2 && expSafe 12 negR && expSafe 12 mExponent &&
    nonneg mRatio && nonneg m && expSafe 12 aInner &&
    positive onePlusR && nonneg aExp && nonneg invOnePlusR &&
    nonneg aRatio && nonneg a && qtSafe 16 m && qtSafe 16 a &&
    nonneg tm && nonneg ta && positive oneMinusM &&
    nonneg invOneMinusM && nonneg uLeft && nonneg uRight0 &&
    nonneg uRight && nonneg u
  ⟨safe, r2, expNegR, mRatio, m, aRatio, a, u⟩

def preliminaryR (t : Interval) : Interval :=
  let t2 := mulNonneg t t
  let t3 := mulNonneg t2 t
  add (add (add (rationalInterval (-1) 4)
    (mul (rationalInterval 2 5) t))
    (mul (rationalInterval 33 200) t2))
    (mul (rationalInterval (-2) 25) t3)

def preliminaryS (t : Interval) : Interval :=
  let t2 := mulNonneg t t
  let t3 := mulNonneg t2 t
  let t4 := mulNonneg t3 t
  add (add (mul (rationalInterval 13 40) t2)
    (mul (rationalInterval 17 200) t3))
    (mul (rationalInterval (-2) 25) t4)

def correction (r r2 expNegR : Interval) : Interval :=
  let p := add (add (rationalInterval (-1) 4)
    (mul (rationalInterval 3 100) r))
    (mul (rationalInterval 2 25) r2)
  mul expNegR p

def commonTail (r r2 u : Interval) : Interval :=
  add (add (neg (divNat u 2))
    (mul (rationalInterval (-7) 20) r))
    (mul (rationalInterval (-13) 100) r2)

structure OuterResult where
  safe : Bool
  parameter : Interval
  coordinateGap : Interval
  slack : Interval
deriving Repr

/-- Small-branch analyzer. `coordinateGap` encloses
`log B₀(t) - log X₁(r)`, while `slack` encloses
`finalSmallNormalizedSlack r`. -/
def small (band : SmallBand) (r : Interval) : OuterResult :=
  let c := common r
  let ratio := smallRatio band r
  let parameter := mulNonneg r ratio
  let negT := neg parameter
  let expNegT := exp 12 negT
  let onePlusR := add (point scale) r
  let qr := q 16 r
  let entropy := mulNonneg onePlusR qr
  let base := add (add entropy (correction r c.r2 c.expNegR))
    (commonTail r c.r2 c.u)
  let onePlusT := add (point scale) parameter
  let logRatio := log 16 ratio
  let logOnePlusT := log 16 onePlusT
  let expR := mul expNegT (preliminaryR parameter)
  let logAWithoutR := sub (sub logRatio logOnePlusT) expR
  let slack := add base (divNat logAWithoutR 2)
  let logB := add (neg logOnePlusT)
    (mul expNegT (preliminaryS parameter))
  let coordinateGap := add (mulNonneg r c.u) logB
  let safe := c.safe && nonneg ratio && positive ratio && nonneg parameter &&
    expSafe 12 negT && logSafe 16 ratio && logSafe 16 onePlusT &&
    qtSafe 16 r && nonneg qr && nonneg onePlusR &&
    decide (0 < parameter.lo) && decide (parameter.hi ≤ scale)
  ⟨safe, parameter, coordinateGap, slack⟩

structure ScalarResult where
  safe : Bool
  slack : Interval
deriving Repr

def directEntropy (r : Interval) : Interval × Bool :=
  let onePlusR := add (point scale) r
  let logOnePlusR := log 16 onePlusR
  let logR := log 16 r
  let invR := inv r
  let entropy := mul onePlusR (mul logOnePlusR invR)
  let safe := positive r && logSafe 16 r && logSafe 16 onePlusR
  (entropy, safe)

def preliminaryFOne : Interval × Bool :=
  let two := rationalInterval 2 1
  let logTwo := log 16 two
  let expNegOne := exp 12 (rationalInterval (-1) 1)
  let out := add (mulNat logTwo 2) (mul (rationalInterval (-19) 200) expNegOne)
  (out, logSafe 16 two && expSafe 12 (rationalInterval (-1) 1))

/-- Hyperbolic-middle normalized-slack analyzer. -/
def middle (r : Interval) : ScalarResult :=
  let c := common r
  let ent := directEntropy r
  let fOne := preliminaryFOne
  let oneMinusR := sub (point scale) r
  let uTerm := neg (divNat (mul oneMinusR c.u) 2)
  let tail := add (add uTerm (mul (rationalInterval (-7) 20) r))
    (mul (rationalInterval (-13) 100) c.r2)
  let logR := log 16 r
  let slack := add (add (add (add ent.1 (correction r c.r2 c.expNegR)) tail)
    (neg (divNat logR 2))) (neg (divNat fOne.1 2))
  ⟨c.safe && ent.2 && fOne.2, slack⟩

/-- Shared large-branch analyzer at a supplied frontier parameter. -/
def largeAt (r parameter : Interval) : OuterResult :=
  let c := common r
  let ent := directEntropy r
  let negT := neg parameter
  let expNegT := exp 12 negT
  let onePlusT := add (point scale) parameter
  let logT := log 16 parameter
  let logOnePlusT := log 16 onePlusT
  let expR := mul expNegT (preliminaryR parameter)
  let logA := sub (sub logT logOnePlusT) expR
  let logB := add (neg logOnePlusT)
    (mul expNegT (preliminaryS parameter))
  let logR := log 16 r
  let base := add (add (add ent.1 (correction r c.r2 c.expNegR))
    (commonTail r c.r2 c.u)) (neg (divNat logR 2))
  let slack := add base (divNat logB 2)
  let coordinateGap := add (mulNonneg r c.u) logA
  let safe := c.safe && ent.2 && nonneg parameter && positive parameter &&
    expSafe 12 negT && logSafe 16 parameter && logSafe 16 onePlusT &&
    decide (0 < parameter.lo) && decide (parameter.hi ≤ scale)
  ⟨safe, parameter, coordinateGap, slack⟩

/-- Exact `t=1` cap analyzer immediately after the A-coordinate crossing. -/
def largeCap (r : Interval) : OuterResult :=
  largeAt r (point scale)

/-- Raw quartic large-branch analyzer beyond `r = 361 / 1000`. -/
def large (band : LargeBand) (r : Interval) : OuterResult :=
  largeAt r (largeParameter band r)

end RamseyLean.FinalCertificate



