import RamseyLean.Analysis.NormalizedFunctions
import Mathlib.Tactic

set_option autoImplicit false

namespace RamseyLean.FixedPointInterval

open Finset

/-! A transparent fixed-point backend at scale `10^12`. -/

def scale : ℤ := 1000000000000

structure Interval where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr

def point (z : ℤ) : Interval := ⟨z, z⟩
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩

def min4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def max4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

/-- Integer floor division; `scale` is positive. -/
def down (z : ℤ) : ℤ := z / scale
/-- Integer ceiling division by `scale`. -/
def up (z : ℤ) : ℤ := -((-z) / scale)

def mul (I J : Interval) : Interval :=
  ⟨down (min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)),
    up (max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi))⟩

def mulNonneg (I J : Interval) : Interval :=
  ⟨down (I.lo * J.lo), up (I.hi * J.hi)⟩

def inv (I : Interval) : Interval :=
  ⟨(scale * scale) / I.hi, -((-(scale * scale)) / I.lo)⟩

def downNat (z : ℤ) (k : ℕ) : ℤ := z / (k : ℤ)
def upNat (z : ℤ) (k : ℕ) : ℤ := -((-z) / (k : ℤ))

def divNat (I : Interval) (k : ℕ) : Interval :=
  ⟨downNat I.lo k, upNat I.hi k⟩

def mulNat (I : Interval) (k : ℕ) : Interval :=
  ⟨I.lo * k, I.hi * k⟩

def abs (I : Interval) : Interval :=
  ⟨0, max |I.lo| |I.hi|⟩

def pow (I : Interval) : ℕ → Interval
  | 0 => point scale
  | n + 1 => mul (pow I n) I

def sumTerms (f : ℕ → Interval) : ℕ → Interval
  | 0 => point 0
  | n + 1 => add (sumTerms f n) (f n)

def expPoly (n : ℕ) (I : Interval) : Interval :=
  sumTerms (fun i => divNat (pow I i) i.factorial) n

def expError (n : ℕ) (I : Interval) : Interval :=
  divNat (mulNat (pow (abs I) n) n.succ) (n.factorial * n)

def exp (n : ℕ) (I : Interval) : Interval :=
  let Plo := expPoly n (point I.lo)
  let Elo := expError n (point I.lo)
  let Phi := expPoly n (point I.hi)
  let Ehi := expError n (point I.hi)
  ⟨Plo.lo - Elo.hi, Phi.hi + Ehi.hi⟩

def logSeries (n : ℕ) (I : Interval) : Interval :=
  sumTerms (fun i => divNat (pow I (2 * i + 1)) (2 * i + 1)) n

def logError (n : ℕ) (I : Interval) : Interval :=
  let numerator := pow (abs I) (2 * n + 1)
  let denominator := add (point scale) (neg (pow I 2))
  mulNonneg numerator (inv denominator)

def logArgument (z : ℤ) : Interval :=
  mul (point (z - scale)) (inv (point (z + scale)))

def log (n : ℕ) (I : Interval) : Interval :=
  let Zlo := logArgument I.lo
  let Plo := logSeries n Zlo
  let Elo := logError n Zlo
  let Zhi := logArgument I.hi
  let Phi := logSeries n Zhi
  let Ehi := logError n Zhi
  mulNat ⟨Plo.lo - Elo.hi, Phi.hi + Ehi.hi⟩ 2

def qPoly (n : ℕ) (I : Interval) : Interval :=
  sumTerms (fun i =>
    let t := divNat (pow I i) (i + 1)
    if Even i then t else neg t) n

def tPoly (n : ℕ) (I : Interval) : Interval :=
  sumTerms (fun i => divNat (pow I i) (i + 1)) n

def ePoly (n : ℕ) (I : Interval) : Interval :=
  sumTerms (fun i =>
    let t := divNat (pow I i) (i + 1).factorial
    if Even i then t else neg t) n

def qtError (n : ℕ) (I : Interval) : Interval :=
  let denominator := add (point scale) (neg I)
  mulNonneg (pow I n) (inv denominator)

def eError (n : ℕ) (I : Interval) : Interval :=
  divNat (mulNat (pow I n) 2) (n + 1).factorial

def q (n : ℕ) (I : Interval) : Interval :=
  let P := qPoly n I
  let E := qtError n I
  ⟨P.lo - E.hi, P.hi + E.hi⟩

def t (n : ℕ) (I : Interval) : Interval :=
  let P := tPoly n I
  let E := qtError n I
  ⟨P.lo - E.hi, P.hi + E.hi⟩

def e (n : ℕ) (I : Interval) : Interval :=
  let P := ePoly n I
  let E := eError n I
  ⟨P.lo - E.hi, P.hi + E.hi⟩

def nonneg (I : Interval) : Bool := decide (0 ≤ I.lo)
def positive (I : Interval) : Bool := decide (0 < I.lo)
def expSafe (n : ℕ) (I : Interval) : Bool :=
  decide (0 < n) && decide (|I.lo| ≤ scale) && decide (|I.hi| ≤ scale)
def qtSafe (n : ℕ) (I : Interval) : Bool :=
  let N := pow I n
  let D := add (point scale) (neg I)
  let Di := inv D
  nonneg I && decide (I.hi < scale) && decide (0 < n) &&
    positive D && nonneg N && nonneg Di
def eSafe (n : ℕ) (I : Interval) : Bool :=
  nonneg I && decide (0 < n) && decide (2 * I.hi ≤ scale * (n + 2))

def logSafe (n : ℕ) (I : Interval) : Bool :=
  let Zlo := logArgument I.lo
  let Zhi := logArgument I.hi
  let Nlo := pow (abs Zlo) (2 * n + 1)
  let Nhi := pow (abs Zhi) (2 * n + 1)
  let Dlo := add (point scale) (neg (pow Zlo 2))
  let Dhi := add (point scale) (neg (pow Zhi 2))
  let Dloi := inv Dlo
  let Dhii := inv Dhi
  decide (0 < n) && decide (0 < I.lo) &&
    decide (0 < I.lo + scale) && decide (0 < I.hi + scale) &&
    positive Dlo && positive Dhi && nonneg Nlo && nonneg Nhi &&
    nonneg Dloi && nonneg Dhii





noncomputable def value (z : ℤ) : ℝ := (z : ℝ) / (scale : ℝ)

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  value I.lo ≤ x ∧ x ≤ value I.hi

theorem scale_pos : (0 : ℤ) < scale := by norm_num [scale]

theorem scale_pos_real : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos

theorem cast_ediv_le_div {a b : ℤ} (hb : 0 < b) :
    ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

theorem div_le_cast_ceil {a b : ℤ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((-((-a) / b) : ℤ) : ℝ) := by
  have h := cast_ediv_le_div (a := -a) hb
  calc
    (a : ℝ) / (b : ℝ) = - (((-a : ℤ) : ℝ) / (b : ℝ)) := by push_cast; ring
    _ ≤ - ((((-a) / b : ℤ) : ℝ)) := neg_le_neg h
    _ = ((-((-a) / b) : ℤ) : ℝ) := by norm_num

@[simp] theorem value_add (a b : ℤ) : value (a + b) = value a + value b := by
  simp [value]
  ring

@[simp] theorem value_neg (a : ℤ) : value (-a) = -value a := by
  unfold value
  push_cast
  ring

theorem value_down_le (z : ℤ) :
    value (down z) ≤ value z / (scale : ℝ) := by
  unfold value down
  exact div_le_div_of_nonneg_right (cast_ediv_le_div scale_pos) scale_pos_real.le

theorem value_le_up (z : ℤ) :
    value z / (scale : ℝ) ≤ value (up z) := by
  unfold value up
  exact div_le_div_of_nonneg_right (div_le_cast_ceil scale_pos) scale_pos_real.le

theorem value_mul_scaled (a b : ℤ) :
    value (a * b) / (scale : ℝ) = value a * value b := by
  unfold value
  push_cast
  field_simp [scale_pos_real.ne']

theorem value_down_mul_le (a b : ℤ) :
    value (down (a * b)) ≤ value a * value b := by
  exact (value_down_le (a * b)).trans_eq (value_mul_scaled a b)

theorem value_mul_le_up (a b : ℤ) :
    value a * value b ≤ value (up (a * b)) := by
  exact (value_mul_scaled a b).symm.trans_le (value_le_up (a * b))

theorem mul_mem_fourCorners {a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  constructor
  · by_cases hy : 0 ≤ y
    · have hxy : a * y ≤ x * y := mul_le_mul_of_nonneg_right hax hy
      by_cases ha : 0 ≤ a
      · calc
          min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c := by simp
          _ ≤ a*y := mul_le_mul_of_nonneg_left hcy ha
          _ ≤ x*y := hxy
      · have ha' : a ≤ 0 := le_of_not_ge ha
        calc
          min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d := by simp
          _ ≤ a*y := mul_le_mul_of_nonpos_left hyd ha'
          _ ≤ x*y := hxy
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hxy : b * y ≤ x * y := mul_le_mul_of_nonpos_right hxb hy'
      by_cases hb : 0 ≤ b
      · calc
          min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c := by simp
          _ ≤ b*y := mul_le_mul_of_nonneg_left hcy hb
          _ ≤ x*y := hxy
      · have hb' : b ≤ 0 := le_of_not_ge hb
        calc
          min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d := by simp
          _ ≤ b*y := mul_le_mul_of_nonpos_left hyd hb'
          _ ≤ x*y := hxy
  · by_cases hy : 0 ≤ y
    · have hxy : x * y ≤ b * y := mul_le_mul_of_nonneg_right hxb hy
      by_cases hb : 0 ≤ b
      · calc
          x*y ≤ b*y := hxy
          _ ≤ b*d := mul_le_mul_of_nonneg_left hyd hb
          _ ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by simp
      · have hb' : b ≤ 0 := le_of_not_ge hb
        calc
          x*y ≤ b*y := hxy
          _ ≤ b*c := mul_le_mul_of_nonpos_left hcy hb'
          _ ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by simp
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hxy : x * y ≤ a * y := mul_le_mul_of_nonpos_right hax hy'
      by_cases ha : 0 ≤ a
      · calc
          x*y ≤ a*y := hxy
          _ ≤ a*d := mul_le_mul_of_nonneg_left hyd ha
          _ ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by simp
      · have ha' : a ≤ 0 := le_of_not_ge ha
        calc
          x*y ≤ a*y := hxy
          _ ≤ a*c := mul_le_mul_of_nonpos_left hcy ha'
          _ ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by simp

namespace Interval

theorem contains_point (z : ℤ) : (point z).Contains (value z) := by
  simp [Contains, point]

theorem Contains.add {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  change value (I.lo + J.lo) ≤ x + y ∧ x + y ≤ value (I.hi + J.hi)
  simp only [value_add]
  exact ⟨add_le_add hxlo hylo, add_le_add hxhi hyhi⟩

theorem Contains.neg {I : Interval} {x : ℝ}
    (hx : I.Contains x) : (neg I).Contains (-x) := by
  rcases hx with ⟨hxlo, hxhi⟩
  change value (-I.hi) ≤ -x ∧ -x ≤ value (-I.lo)
  simp only [value_neg]
  exact ⟨neg_le_neg hxhi, neg_le_neg hxlo⟩

private noncomputable def scaledValue (z : ℤ) : ℝ := value z / (scale : ℝ)

@[simp] private theorem scaledValue_min (a b : ℤ) :
    scaledValue (min a b) = min (scaledValue a) (scaledValue b) := by
  by_cases h : a ≤ b
  · have hv : value a ≤ value b := by
      unfold value
      exact div_le_div_of_nonneg_right (by exact_mod_cast h) scale_pos_real.le
    have hsv : scaledValue a ≤ scaledValue b :=
      div_le_div_of_nonneg_right hv scale_pos_real.le
    simp [min_eq_left h, min_eq_left hsv]
  · have h' : b ≤ a := le_of_not_ge h
    have hv : value b ≤ value a := by
      unfold value
      exact div_le_div_of_nonneg_right (by exact_mod_cast h') scale_pos_real.le
    have hsv : scaledValue b ≤ scaledValue a :=
      div_le_div_of_nonneg_right hv scale_pos_real.le
    simp [min_eq_right h', min_eq_right hsv]

@[simp] private theorem scaledValue_mul (a b : ℤ) :
    scaledValue (a * b) = value a * value b :=
  value_mul_scaled a b

@[simp] private theorem scaledValue_max (a b : ℤ) :
    scaledValue (max a b) = max (scaledValue a) (scaledValue b) := by
  by_cases h : a ≤ b
  · have hv : value a ≤ value b := by
      unfold value
      exact div_le_div_of_nonneg_right (by exact_mod_cast h) scale_pos_real.le
    have hsv : scaledValue a ≤ scaledValue b :=
      div_le_div_of_nonneg_right hv scale_pos_real.le
    simp [max_eq_right h, max_eq_right hsv]
  · have h' : b ≤ a := le_of_not_ge h
    have hv : value b ≤ value a := by
      unfold value
      exact div_le_div_of_nonneg_right (by exact_mod_cast h') scale_pos_real.le
    have hsv : scaledValue b ≤ scaledValue a :=
      div_le_div_of_nonneg_right hv scale_pos_real.le
    simp [max_eq_left h', max_eq_left hsv]

private theorem value_min4_mul (I J : Interval) :
    value (min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)) /
        (scale : ℝ) =
      min (min (value I.lo * value J.lo) (value I.lo * value J.hi))
        (min (value I.hi * value J.lo) (value I.hi * value J.hi)) := by
  change scaledValue (min4 (I.lo * J.lo) (I.lo * J.hi)
    (I.hi * J.lo) (I.hi * J.hi)) = _
  simp only [min4, scaledValue_min, scaledValue_mul]

private theorem value_max4_mul (I J : Interval) :
    value (max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)) /
        (scale : ℝ) =
      max (max (value I.lo * value J.lo) (value I.lo * value J.hi))
        (max (value I.hi * value J.lo) (value I.hi * value J.hi)) := by
  change scaledValue (max4 (I.lo * J.lo) (I.lo * J.hi)
    (I.hi * J.lo) (I.hi * J.hi)) = _
  simp only [max4, scaledValue_max, scaledValue_mul]

theorem Contains.mul {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  have hfour := mul_mem_fourCorners hx.1 hx.2 hy.1 hy.2
  constructor
  · exact ((value_down_le _).trans_eq (value_min4_mul I J)).trans hfour.1
  · exact hfour.2.trans ((value_max4_mul I J).symm.trans_le (value_le_up _))

theorem Contains.mulNonneg {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
    (mulNonneg I J).Contains (x * y) := by
  have hIr : 0 ≤ value I.lo := by
    unfold value
    exact div_nonneg (by exact_mod_cast hI) scale_pos_real.le
  have hJr : 0 ≤ value J.lo := by
    unfold value
    exact div_nonneg (by exact_mod_cast hJ) scale_pos_real.le
  constructor
  · exact (value_down_mul_le I.lo J.lo).trans
      (mul_le_mul hx.1 hy.1 hJr (hIr.trans hx.1))
  · exact (mul_le_mul hx.2 hy.2 (hJr.trans hy.1)
      ((hIr.trans hx.1).trans hx.2)).trans (value_mul_le_up I.hi J.hi)


theorem value_invFloor_le (z : ℤ) (hz : 0 < z) :
    value ((scale * scale) / z) ≤ (value z)⁻¹ := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have h := cast_ediv_le_div (a := scale * scale) hz
  unfold value
  calc
    (((scale * scale) / z : ℤ) : ℝ) / (scale : ℝ) ≤
        (((scale * scale : ℤ) : ℝ) / (z : ℝ)) / (scale : ℝ) :=
      div_le_div_of_nonneg_right h scale_pos_real.le
    _ = (((z : ℝ) / (scale : ℝ)))⁻¹ := by
      push_cast
      field_simp [scale_pos_real.ne', hzR.ne']

theorem value_inv_le_ceil (z : ℤ) (hz : 0 < z) :
    (value z)⁻¹ ≤ value (-((-(scale * scale)) / z)) := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have h := div_le_cast_ceil (a := scale * scale) hz
  unfold value
  calc
    (((z : ℝ) / (scale : ℝ)))⁻¹ =
        (((scale * scale : ℤ) : ℝ) / (z : ℝ)) / (scale : ℝ) := by
      push_cast
      field_simp [scale_pos_real.ne', hzR.ne']
    _ ≤ ((-((-(scale * scale)) / z) : ℤ) : ℝ) / (scale : ℝ) :=
      div_le_div_of_nonneg_right h scale_pos_real.le

theorem Contains.inv {I : Interval} {x : ℝ}
    (hx : I.Contains x) (hlo : 0 < I.lo) : (inv I).Contains x⁻¹ := by
  have hloValue : 0 < value I.lo := by
    unfold value
    exact div_pos (by exact_mod_cast hlo) scale_pos_real
  have hxpos : 0 < x := hloValue.trans_le hx.1
  have hhiValue : 0 < value I.hi := hxpos.trans_le hx.2
  have hhiCast : (0 : ℝ) < (I.hi : ℝ) := by
    have := mul_pos hhiValue scale_pos_real
    simpa [value, div_mul_cancel₀ _ scale_pos_real.ne'] using this
  have hhi : 0 < I.hi := by exact_mod_cast hhiCast
  constructor
  · exact (value_invFloor_le I.hi hhi).trans ((inv_le_inv₀ hhiValue hxpos).2 hx.2)
  · exact ((inv_le_inv₀ hxpos hloValue).2 hx.1).trans (value_inv_le_ceil I.lo hlo)

theorem value_downNat_le (z : ℤ) {k : ℕ} (hk : 0 < k) :
    value (downNat z k) ≤ value z / (k : ℝ) := by
  have hkInt : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have h := cast_ediv_le_div (a := z) hkInt
  unfold value downNat
  calc
    (((z / (k : ℤ) : ℤ) : ℝ) / (scale : ℝ)) ≤
        (((z : ℝ) / (k : ℝ)) / (scale : ℝ)) :=
      div_le_div_of_nonneg_right (by simpa using h) scale_pos_real.le
    _ = ((z : ℝ) / (scale : ℝ)) / (k : ℝ) := by
      field_simp [scale_pos_real.ne', (by positivity : (k : ℝ) ≠ 0)]

theorem value_le_upNat (z : ℤ) {k : ℕ} (hk : 0 < k) :
    value z / (k : ℝ) ≤ value (upNat z k) := by
  have hkInt : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have h := div_le_cast_ceil (a := z) hkInt
  unfold value upNat
  calc
    ((z : ℝ) / (scale : ℝ)) / (k : ℝ) =
        (((z : ℝ) / (k : ℝ)) / (scale : ℝ)) := by
      field_simp [scale_pos_real.ne', (by positivity : (k : ℝ) ≠ 0)]
    _ ≤ (((-((-z) / (k : ℤ)) : ℤ) : ℝ) / (scale : ℝ)) :=
      div_le_div_of_nonneg_right (by simpa using h) scale_pos_real.le

theorem Contains.divNat {I : Interval} {x : ℝ} {k : ℕ}
    (hx : I.Contains x) (hk : 0 < k) : (divNat I k).Contains (x / k) := by
  constructor
  · exact (value_downNat_le I.lo hk).trans
      (div_le_div_of_nonneg_right hx.1 (by positivity))
  · exact (div_le_div_of_nonneg_right hx.2 (by positivity)).trans
      (value_le_upNat I.hi hk)

@[simp] theorem value_mulNat (z : ℤ) (k : ℕ) :
    value (z * k) = value z * k := by
  unfold value
  push_cast
  ring

theorem Contains.mulNat {I : Interval} {x : ℝ} {k : ℕ}
    (hx : I.Contains x) : (mulNat I k).Contains (x * k) := by
  change value (I.lo * k) ≤ x * k ∧ x * k ≤ value (I.hi * k)
  simp only [value_mulNat]
  exact ⟨mul_le_mul_of_nonneg_right hx.1 (by positivity),
    mul_le_mul_of_nonneg_right hx.2 (by positivity)⟩

@[simp] theorem value_abs (z : ℤ) : value |z| = |value z| := by
  unfold value
  rw [Int.cast_abs, abs_div, abs_of_pos scale_pos_real]

@[simp] theorem value_max (a b : ℤ) : value (max a b) = max (value a) (value b) := by
  by_cases h : a ≤ b
  · have hv : value a ≤ value b := by
      unfold value
      exact div_le_div_of_nonneg_right (by exact_mod_cast h) scale_pos_real.le
    simp [max_eq_right h, max_eq_right hv]
  · have h' : b ≤ a := le_of_not_ge h
    have hv : value b ≤ value a := by
      unfold value
      exact div_le_div_of_nonneg_right (by exact_mod_cast h') scale_pos_real.le
    simp [max_eq_left h', max_eq_left hv]

theorem Contains.abs {I : Interval} {x : ℝ}
    (hx : I.Contains x) : (abs I).Contains |x| := by
  constructor
  · change value 0 ≤ |x|
    simpa [value] using abs_nonneg x
  · change |x| ≤ value (max |I.lo| |I.hi|)
    rw [value_max, value_abs, value_abs, abs_le]
    constructor
    · calc
        -max |value I.lo| |value I.hi| ≤ -|value I.lo| :=
          neg_le_neg (le_max_left _ _)
        _ ≤ value I.lo := neg_abs_le _
        _ ≤ x := hx.1
    · calc
        x ≤ value I.hi := hx.2
        _ ≤ |value I.hi| := le_abs_self _
        _ ≤ max |value I.lo| |value I.hi| := le_max_right _ _

theorem Contains.pow {I : Interval} {x : ℝ}
    (hx : I.Contains x) : ∀ n : ℕ, (pow I n).Contains (x ^ n)
  | 0 => by
      change (point scale).Contains 1
      simpa [value, scale] using contains_point scale
  | n + 1 => by
      rw [pow_succ]
      exact (Contains.pow hx n).mul hx

theorem contains_sumTerms {F : ℕ → Interval} {f : ℕ → ℝ} :
    ∀ n : ℕ, (∀ i < n, (F i).Contains (f i)) →
      (sumTerms F n).Contains (∑ i ∈ Finset.range n, f i)
  | 0, _ => by simpa [sumTerms, value] using contains_point 0
  | n + 1, h => by
      rw [Finset.sum_range_succ]
      exact (contains_sumTerms n (fun i hi => h i (hi.trans n.lt_succ_self))).add
        (h n n.lt_succ_self)


theorem Contains.expPoly {I : Interval} {x : ℝ}
    (hx : I.Contains x) (n : ℕ) :
    (FixedPointInterval.expPoly n I).Contains
      (CertifiedNumerics.expPoly n x) := by
  unfold FixedPointInterval.expPoly CertifiedNumerics.expPoly
  apply contains_sumTerms
  intro i hi
  exact (hx.pow i).divNat (Nat.factorial_pos i)

theorem Contains.expError {I : Interval} {x : ℝ}
    (hx : I.Contains x) {n : ℕ} (hn : 0 < n) :
    (FixedPointInterval.expError n I).Contains
      (CertifiedNumerics.expError n x) := by
  have hden : 0 < n.factorial * n := mul_pos (Nat.factorial_pos n) hn
  have h := ((hx.abs.pow n).mulNat (k := n.succ)).divNat hden
  convert h using 1
  · rfl
  · unfold CertifiedNumerics.expError
    push_cast
    field_simp

theorem Contains.exp {I : Interval} {x : ℝ}
    (hx : I.Contains x) {n : ℕ} (hn : 0 < n)
    (hlo : |value I.lo| ≤ 1) (hhi : |value I.hi| ≤ 1) :
    (FixedPointInterval.exp n I).Contains (Real.exp x) := by
  let Plo := FixedPointInterval.expPoly n (point I.lo)
  let Elo := FixedPointInterval.expError n (point I.lo)
  let Phi := FixedPointInterval.expPoly n (point I.hi)
  let Ehi := FixedPointInterval.expError n (point I.hi)
  have hpLo := (contains_point I.lo).expPoly n
  have heLo := (contains_point I.lo).expError hn
  have hpHi := (contains_point I.hi).expPoly n
  have heHi := (contains_point I.hi).expError hn
  have hLower :
      value (Plo.lo - Elo.hi) ≤
        CertifiedNumerics.expPoly n (value I.lo) -
          CertifiedNumerics.expError n (value I.lo) := by
    dsimp [Plo, Elo] at hpLo heLo ⊢
    rw [show value
      ((FixedPointInterval.expPoly n (point I.lo)).lo -
        (FixedPointInterval.expError n (point I.lo)).hi) =
      value (FixedPointInterval.expPoly n (point I.lo)).lo -
        value (FixedPointInterval.expError n (point I.lo)).hi by
          simp [sub_eq_add_neg]]
    linarith [hpLo.1, heLo.2]
  have hUpper :
      CertifiedNumerics.expPoly n (value I.hi) +
          CertifiedNumerics.expError n (value I.hi) ≤
        value (Phi.hi + Ehi.hi) := by
    dsimp [Phi, Ehi] at hpHi heHi ⊢
    rw [value_add]
    linarith [hpHi.2, heHi.2]
  have hmain := CertifiedNumerics.exp_on_interval hx hlo hhi hn hLower hUpper
  change value (Plo.lo - Elo.hi) ≤ Real.exp x ∧
    Real.exp x ≤ value (Phi.hi + Ehi.hi)
  exact hmain


theorem Contains.logSeries {I : Interval} {z : ℝ}
    (hz : I.Contains z) (n : ℕ) :
    (FixedPointInterval.logSeries n I).Contains
      (CertifiedNumerics.logSeries n z) := by
  unfold FixedPointInterval.logSeries CertifiedNumerics.logSeries
  apply contains_sumTerms n
  intro i hi
  have h := Contains.divNat (Contains.pow hz (2 * i + 1))
    (k := 2 * i + 1) (by omega)
  convert h using 1 <;> push_cast <;> ring

theorem Contains.logError {I : Interval} {z : ℝ} (hz : I.Contains z)
    (n : ℕ)
    (hden : 0 < (FixedPointInterval.add (point scale)
      (FixedPointInterval.neg (FixedPointInterval.pow I 2))).lo)
    (hnum : 0 ≤ (FixedPointInterval.pow (FixedPointInterval.abs I)
      (2 * n + 1)).lo)
    (hinv : 0 ≤ (FixedPointInterval.inv (FixedPointInterval.add (point scale)
      (FixedPointInterval.neg (FixedPointInterval.pow I 2)))).lo) :
    (FixedPointInterval.logError n I).Contains
      (CertifiedNumerics.logError n z) := by
  have hone : (point scale).Contains (1 : ℝ) := by
    simpa [value, scale] using contains_point scale
  have hdenContains :
      (FixedPointInterval.add (point scale)
        (FixedPointInterval.neg (FixedPointInterval.pow I 2))).Contains
        (1 - z ^ 2) := by
    convert hone.add (Contains.pow hz 2).neg using 1 <;> ring
  have hInv := Contains.inv hdenContains hden
  have hNum := hz.abs.pow (2 * n + 1)
  have h := Contains.mulNonneg hNum hInv hnum hinv
  unfold FixedPointInterval.logError CertifiedNumerics.logError
  exact h

theorem logArgument_contains (z : ℤ) (hz : 0 < z + scale) :
    (logArgument z).Contains ((value z - 1) / (value z + 1)) := by
  have hzPoint := contains_point z
  have hone : (point scale).Contains (1 : ℝ) := by
    simpa [value, scale] using contains_point scale
  have hplus := hzPoint.add hone
  have hplusInv := hplus.inv (by simpa [FixedPointInterval.add, point] using hz)
  have h := (hzPoint.add hone.neg).mul hplusInv
  simpa [logArgument, FixedPointInterval.add, FixedPointInterval.neg, point,
    sub_eq_add_neg, div_eq_mul_inv] using h

end Interval


def checkLower (I : Interval) (z : ℤ) : Bool := decide (z < I.lo)

def checkLowerEq (I : Interval) (z : ℤ) : Bool := decide (z ≤ I.lo)


theorem value_lt_of_checkLower {I : Interval} {x : ℝ} {z : ℤ}
    (hcheck : checkLower I z = true) (hx : I.Contains x) :
    value z < x := by
  have hzlo : z < I.lo := by simpa [checkLower] using hcheck
  have hv : value z < value I.lo := by
    unfold value
    exact div_lt_div_of_pos_right (by exact_mod_cast hzlo) scale_pos_real
  exact hv.trans_le hx.1

theorem value_le_of_checkLowerEq {I : Interval} {x : ℝ} {z : ℤ}
    (hcheck : checkLowerEq I z = true) (hx : I.Contains x) :
    value z ≤ x := by
  have hzlo : z ≤ I.lo := by simpa [checkLowerEq] using hcheck
  have hv : value z ≤ value I.lo := by
    unfold value
    exact div_le_div_of_nonneg_right (by exact_mod_cast hzlo) scale_pos_real.le
  exact hv.trans hx.1

namespace Sound

theorem value_sub_sound (a b : ℤ) :
    value (a - b) = value a - value b := by
  simp [sub_eq_add_neg]

theorem value_mul_two_sound (a : ℤ) :
    value (a * 2) = value a * 2 := by
  unfold value
  push_cast
  ring

theorem contains_error_enclosure {P E : Interval} {f p err : ℝ}
    (hp : P.Contains p) (he : E.Contains err)
    (hmain : |f - p| ≤ err) :
    ({ lo := P.lo - E.hi, hi := P.hi + E.hi } : Interval).Contains f := by
  unfold Interval.Contains
  change value (P.lo - E.hi) ≤ f ∧ f ≤ value (P.hi + E.hi)
  rw [value_sub_sound, value_add, abs_le] at *
  constructor <;> linarith [hp.1, hp.2, he.1, he.2]

theorem contains_two_endpoint_enclosure
    {Plo Elo Phi Ehi : Interval} {f pLo eLo pHi eHi : ℝ}
    (hpLo : Plo.Contains pLo) (heLo : Elo.Contains eLo)
    (hpHi : Phi.Contains pHi) (heHi : Ehi.Contains eHi)
    (hlower : 2 * (pLo - eLo) ≤ f)
    (hupper : f ≤ 2 * (pHi + eHi)) :
    (mulNat { lo := Plo.lo - Elo.hi, hi := Phi.hi + Ehi.hi } 2).Contains f := by
  unfold Interval.Contains
  change value ((Plo.lo - Elo.hi) * (2 : ℤ)) ≤ f ∧
    f ≤ value ((Phi.hi + Ehi.hi) * (2 : ℤ))
  rw [value_mul_two_sound, value_mul_two_sound,
    value_sub_sound, value_add]
  norm_num at ⊢
  constructor <;>
    linarith [hpLo.1, hpLo.2, heLo.1, heLo.2,
      hpHi.1, hpHi.2, heHi.1, heHi.2]

theorem contains_logSeries {I : Interval} {z : ℝ} (hz : I.Contains z) (n : ℕ) :
    (logSeries n I).Contains (CertifiedNumerics.logSeries n z) := by
  unfold logSeries CertifiedNumerics.logSeries
  apply Interval.contains_sumTerms n
  intro i hi
  have h := Interval.Contains.divNat (Interval.Contains.pow hz (2 * i + 1))
    (k := 2 * i + 1) (by omega)
  convert h using 1 <;> push_cast <;> ring

theorem contains_logError {I : Interval} {z : ℝ} (hz : I.Contains z)
    (n : ℕ)
    (hden : 0 < (add (point scale) (neg (pow I 2))).lo)
    (hnum : 0 ≤ (pow (abs I) (2 * n + 1)).lo)
    (hinv : 0 ≤ (inv (add (point scale) (neg (pow I 2)))).lo) :
    (logError n I).Contains (CertifiedNumerics.logError n z) := by
  have hone : (point scale).Contains (1 : ℝ) := by
    simpa [value, scale] using Interval.contains_point scale
  have hdenContains : (add (point scale) (neg (pow I 2))).Contains (1 - z ^ 2) := by
    convert hone.add (Interval.Contains.pow hz 2).neg using 1 <;> ring
  have hInv := Interval.Contains.inv hdenContains hden
  have hNum := hz.abs.pow (2 * n + 1)
  have h := Interval.Contains.mulNonneg hNum hInv hnum hinv
  unfold logError CertifiedNumerics.logError
  exact h

theorem contains_logArgument (z : ℤ) (hz : 0 < z + scale) :
    (logArgument z).Contains ((value z - 1) / (value z + 1)) := by
  have hzPoint := Interval.contains_point z
  have hone : (point scale).Contains (1 : ℝ) := by
    simpa [value, scale] using Interval.contains_point scale
  have hplus := hzPoint.add hone
  have hplusInv := hplus.inv (by simpa [add, point] using hz)
  have h := (hzPoint.add hone.neg).mul hplusInv
  simpa [logArgument, add, neg, point, sub_eq_add_neg, div_eq_mul_inv] using h

theorem contains_log {I : Interval} {q : ℝ} (hqI : I.Contains q)
    (n : ℕ) (hlo : 0 < I.lo)
    (hloPlus : 0 < I.lo + scale) (hhiPlus : 0 < I.hi + scale)
    (hdenLo : 0 < (add (point scale) (neg (pow (logArgument I.lo) 2))).lo)
    (hdenHi : 0 < (add (point scale) (neg (pow (logArgument I.hi) 2))).lo)
    (hnumLo : 0 ≤ (pow (abs (logArgument I.lo)) (2 * n + 1)).lo)
    (hnumHi : 0 ≤ (pow (abs (logArgument I.hi)) (2 * n + 1)).lo)
    (hinvLo : 0 ≤
      (inv (add (point scale) (neg (pow (logArgument I.lo) 2)))).lo)
    (hinvHi : 0 ≤
      (inv (add (point scale) (neg (pow (logArgument I.hi) 2)))).lo) :
    (log n I).Contains (Real.log q) := by
  let a := value I.lo
  let b := value I.hi
  let za := (a - 1) / (a + 1)
  let zb := (b - 1) / (b + 1)
  have haI := contains_logArgument I.lo hloPlus
  have hbI := contains_logArgument I.hi hhiPlus
  have hpLo := contains_logSeries haI n
  have heLo := contains_logError haI n hdenLo hnumLo hinvLo
  have hpHi := contains_logSeries hbI n
  have heHi := contains_logError hbI n hdenHi hnumHi hinvHi
  have haCast : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
  have ha : 0 < a := by
    dsimp [a, value]
    exact div_pos haCast scale_pos_real
  have hq : 0 < q := ha.trans_le hqI.1
  have hb : 0 < b := hq.trans_le hqI.2
  have htLo := CertifiedNumerics.log_taylor_mem ha n
  have htHi := CertifiedNumerics.log_taylor_mem hb n
  have hlogLo : Real.log a ≤ Real.log q :=
    Real.strictMonoOn_log.monotoneOn ha hq hqI.1
  have hlogHi : Real.log q ≤ Real.log b :=
    Real.strictMonoOn_log.monotoneOn hq hb hqI.2
  have hlower :
      2 * (CertifiedNumerics.logSeries n ((value I.lo - 1) / (value I.lo + 1)) -
        CertifiedNumerics.logError n ((value I.lo - 1) / (value I.lo + 1))) ≤
        Real.log q := htLo.1.trans hlogLo
  have hupper :
      Real.log q ≤
        2 * (CertifiedNumerics.logSeries n ((value I.hi - 1) / (value I.hi + 1)) +
          CertifiedNumerics.logError n ((value I.hi - 1) / (value I.hi + 1))) :=
    hlogHi.trans htHi.2
  simpa [log] using
    contains_two_endpoint_enclosure hpLo heLo hpHi heHi hlower hupper

theorem logOnePlusRatioPoly_eq_ite (n : ℕ) (u : ℝ) :
    CertifiedNumerics.logOnePlusRatioPoly n u =
      ∑ i ∈ range n,
        if Even i then u ^ i / (i + 1) else -(u ^ i / (i + 1)) := by
  unfold CertifiedNumerics.logOnePlusRatioPoly
  apply sum_congr rfl
  intro i hi
  rw [neg_one_pow_eq_ite]
  split_ifs <;> ring

theorem contains_qPoly {I : Interval} {u : ℝ} (hu : I.Contains u) (n : ℕ) :
    (qPoly n I).Contains (CertifiedNumerics.logOnePlusRatioPoly n u) := by
  rw [logOnePlusRatioPoly_eq_ite]
  unfold qPoly
  apply Interval.contains_sumTerms n
  intro i hi
  split_ifs with hEven
  · have h := Interval.Contains.divNat (Interval.Contains.pow hu i)
      (k := i + 1) (by omega)
    convert h using 1 <;> push_cast <;> ring
  · have h := (Interval.Contains.divNat (Interval.Contains.pow hu i)
      (k := i + 1) (by omega)).neg
    convert h using 1 <;> push_cast <;> ring

theorem contains_tPoly {I : Interval} {u : ℝ} (hu : I.Contains u) (n : ℕ) :
    (tPoly n I).Contains (CertifiedNumerics.negLogOneSubRatioPoly n u) := by
  unfold tPoly CertifiedNumerics.negLogOneSubRatioPoly
  apply Interval.contains_sumTerms n
  intro i hi
  have h := Interval.Contains.divNat (Interval.Contains.pow hu i)
    (k := i + 1) (by omega)
  convert h using 1 <;> push_cast <;> ring

theorem oneSubExpNegRatioPoly_eq_ite (n : ℕ) (v : ℝ) :
    CertifiedNumerics.oneSubExpNegRatioPoly n v =
      ∑ i ∈ range n,
        if Even i then v ^ i / (i + 1).factorial
        else -(v ^ i / (i + 1).factorial) := by
  unfold CertifiedNumerics.oneSubExpNegRatioPoly
  apply sum_congr rfl
  intro i hi
  rw [neg_one_pow_eq_ite]
  split_ifs <;> ring

theorem contains_ePoly {I : Interval} {v : ℝ} (hv : I.Contains v) (n : ℕ) :
    (ePoly n I).Contains (CertifiedNumerics.oneSubExpNegRatioPoly n v) := by
  rw [oneSubExpNegRatioPoly_eq_ite]
  unfold ePoly
  apply Interval.contains_sumTerms n
  intro i hi
  split_ifs with hEven
  · exact Interval.Contains.divNat (Interval.Contains.pow hv i)
      (k := (i + 1).factorial) (Nat.factorial_pos (i + 1))
  · exact (Interval.Contains.divNat (Interval.Contains.pow hv i)
      (k := (i + 1).factorial) (Nat.factorial_pos (i + 1))).neg

theorem contains_qtError {I : Interval} {u : ℝ} (hu : I.Contains u) (n : ℕ)
    (hden : 0 < (add (point scale) (neg I)).lo)
    (hnum : 0 ≤ (pow I n).lo)
    (hinv : 0 ≤ (inv (add (point scale) (neg I))).lo) :
    (qtError n I).Contains (CertifiedNumerics.negLogOneSubRatioError n u) := by
  have hone : (point scale).Contains (1 : ℝ) := by
    simpa [value, scale] using Interval.contains_point scale
  have hDen := hone.add hu.neg
  have hInv := Interval.Contains.inv hDen hden
  have h := (Interval.Contains.pow hu n).mulNonneg hInv hnum hinv
  unfold qtError CertifiedNumerics.negLogOneSubRatioError
  exact h

theorem contains_eError {I : Interval} {v : ℝ} (hv : I.Contains v) (n : ℕ) :
    (eError n I).Contains (CertifiedNumerics.oneSubExpNegRatioError n v) := by
  have hmul := Interval.Contains.mulNat (Interval.Contains.pow hv n) (k := 2)
  have h := Interval.Contains.divNat hmul (Nat.factorial_pos (n + 1))
  unfold eError CertifiedNumerics.oneSubExpNegRatioError
  convert h using 1 <;> push_cast <;> ring

theorem contains_q {I : Interval} {u : ℝ} (huI : I.Contains u)
    {n : ℕ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hn : 0 < n)
    (hden : 0 < (add (point scale) (neg I)).lo)
    (hnum : 0 ≤ (pow I n).lo)
    (hinv : 0 ≤ (inv (add (point scale) (neg I))).lo) :
    (q n I).Contains (CertifiedNumerics.logOnePlusRatio u) := by
  have hp := contains_qPoly huI n
  have he0 := contains_qtError huI n hden hnum hinv
  have he : (qtError n I).Contains
      (CertifiedNumerics.logOnePlusRatioError n u) := by
    simpa [CertifiedNumerics.logOnePlusRatioError,
      CertifiedNumerics.negLogOneSubRatioError] using he0
  have hmain :=
    CertifiedNumerics.logOnePlusRatio_taylor_mem hu0 hu1 hn
  simpa [q] using contains_error_enclosure hp he hmain

theorem contains_t {I : Interval} {u : ℝ} (huI : I.Contains u)
    {n : ℕ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hn : 0 < n)
    (hden : 0 < (add (point scale) (neg I)).lo)
    (hnum : 0 ≤ (pow I n).lo)
    (hinv : 0 ≤ (inv (add (point scale) (neg I))).lo) :
    (t n I).Contains (CertifiedNumerics.negLogOneSubRatio u) := by
  have hp := contains_tPoly huI n
  have he := contains_qtError huI n hden hnum hinv
  have hmain :=
    CertifiedNumerics.negLogOneSubRatio_taylor_mem hu0 hu1 hn
  simpa [t] using contains_error_enclosure hp he hmain

theorem contains_e {I : Interval} {v : ℝ} (hvI : I.Contains v)
    {n : ℕ} (hv0 : 0 ≤ v) (hn : 0 < n)
    (hscale : v / (n + 2) ≤ 1 / 2) :
    (e n I).Contains (CertifiedNumerics.oneSubExpNegRatio v) := by
  have hp := contains_ePoly hvI n
  have he := contains_eError hvI n
  have hmain :=
    CertifiedNumerics.oneSubExpNegRatio_taylor_mem hv0 hn hscale
  simpa [e] using contains_error_enclosure hp he hmain

theorem contains_exp_of_safe {I : Interval} {x : ℝ} (hx : I.Contains x)
    {n : ℕ} (hsafe : expSafe n I = true) :
    (exp n I).Contains (Real.exp x) := by
  simp only [expSafe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  rcases hsafe with ⟨⟨hn, hlo⟩, hhi⟩
  apply Interval.Contains.exp hx hn
  · unfold value
    rw [abs_div, abs_of_pos scale_pos_real, div_le_one₀ scale_pos_real]
    exact_mod_cast hlo
  · unfold value
    rw [abs_div, abs_of_pos scale_pos_real, div_le_one₀ scale_pos_real]
    exact_mod_cast hhi

theorem contains_log_of_safe {I : Interval} {q : ℝ} (hq : I.Contains q)
    {n : ℕ} (hsafe : logSafe n I = true) :
    (log n I).Contains (Real.log q) := by
  simp only [logSafe, positive, nonneg, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  rcases hsafe with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hlo⟩, hloPlus⟩, hhiPlus⟩, hdenLo⟩, hdenHi⟩,
      hnumLo⟩, hnumHi⟩, hinvLo⟩, hinvHi⟩
  exact contains_log hq n hlo hloPlus hhiPlus hdenLo hdenHi
    hnumLo hnumHi hinvLo hinvHi

theorem contains_q_of_safe {I : Interval} {u : ℝ} (hu : I.Contains u)
    {n : ℕ} (hsafe : qtSafe n I = true) :
    (q n I).Contains (CertifiedNumerics.logOnePlusRatio u) := by
  simp only [qtSafe, nonneg, positive, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  rcases hsafe with ⟨⟨⟨⟨⟨hI, hhi⟩, hn⟩, hden⟩, hnum⟩, hinv⟩
  have hloValue : 0 ≤ value I.lo := by
    unfold value
    exact div_nonneg (by exact_mod_cast hI) scale_pos_real.le
  have hu0 : 0 ≤ u := hloValue.trans hu.1
  have hhiCast : (I.hi : ℝ) < (scale : ℝ) := by exact_mod_cast hhi
  have hhiValue : value I.hi < 1 := by
    unfold value
    rwa [div_lt_one scale_pos_real]
  have hu1 : u < 1 := hu.2.trans_lt hhiValue
  exact contains_q hu hu0 hu1 hn hden hnum hinv

theorem contains_t_of_safe {I : Interval} {u : ℝ} (hu : I.Contains u)
    {n : ℕ} (hsafe : qtSafe n I = true) :
    (t n I).Contains (CertifiedNumerics.negLogOneSubRatio u) := by
  simp only [qtSafe, nonneg, positive, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  rcases hsafe with ⟨⟨⟨⟨⟨hI, hhi⟩, hn⟩, hden⟩, hnum⟩, hinv⟩
  have hloValue : 0 ≤ value I.lo := by
    unfold value
    exact div_nonneg (by exact_mod_cast hI) scale_pos_real.le
  have hu0 : 0 ≤ u := hloValue.trans hu.1
  have hhiCast : (I.hi : ℝ) < (scale : ℝ) := by exact_mod_cast hhi
  have hhiValue : value I.hi < 1 := by
    unfold value
    rwa [div_lt_one scale_pos_real]
  have hu1 : u < 1 := hu.2.trans_lt hhiValue
  exact contains_t hu hu0 hu1 hn hden hnum hinv

theorem contains_e_of_safe {I : Interval} {v : ℝ} (hv : I.Contains v)
    {n : ℕ} (hsafe : eSafe n I = true) :
    (e n I).Contains (CertifiedNumerics.oneSubExpNegRatio v) := by
  simp only [eSafe, nonneg, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  rcases hsafe with ⟨⟨hI, hn⟩, hbound⟩
  have hloValue : 0 ≤ value I.lo := by
    unfold value
    exact div_nonneg (by exact_mod_cast hI) scale_pos_real.le
  have hv0 : 0 ≤ v := hloValue.trans hv.1
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hboundReal :
      2 * (I.hi : ℝ) ≤ (scale : ℝ) * ((n : ℝ) + 2) := by
    exact_mod_cast hbound
  have hhiScale : value I.hi / ((n : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn2]
    unfold value
    rw [div_le_iff₀ scale_pos_real]
    norm_num [scale] at hboundReal ⊢
    linarith
  have hvScale : v / ((n : ℝ) + 2) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right hv.2 hn2.le).trans hhiScale
  exact contains_e hv hv0 hn hvScale

end Sound

end RamseyLean.FixedPointInterval
































