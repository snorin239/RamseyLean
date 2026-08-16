import RamseyLean.Analysis.CertifiedNumerics
import Mathlib.Tactic

/-!
# Normalized elementary functions for numerical certificates

This module gives total versions of three removable quotients used in the
normalized numerical proof of paper Lemma `lem:numerics`:

* `logOnePlusRatio u = log (1 + u) / u`,
* `negLogOneSubRatio u = -log (1 - u) / u`, and
* `oneSubExpNegRatio v = (1 - exp (-v)) / v`.

All three take the limiting value `1` at zero.  Their Taylor enclosures are
proved from the kernel-checked estimates in `CertifiedNumerics`; the interval
forms use sign-aware endpoint sums, leaving only exact rational arithmetic in
concrete certificates.
-/

set_option autoImplicit false

namespace RamseyLean.CertifiedNumerics

open Finset

noncomputable section

/-! ## The quotient `log (1 + u) / u` -/

/-- The removable quotient `log (1 + u) / u`, extended continuously by `1`
at zero. -/
def logOnePlusRatio (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.log (1 + u) / u

/-- Away from the removable singularity, `logOnePlusRatio` is the usual
quotient. -/
theorem logOnePlusRatio_eq_of_ne {u : ℝ} (hu : u ≠ 0) :
    logOnePlusRatio u = Real.log (1 + u) / u := by
  simp [logOnePlusRatio, hu]

/-- Taylor error used for `logOnePlusRatio`. -/
def logOnePlusRatioError (n : ℕ) (u : ℝ) : ℝ := u ^ n / (1 - u)

/-- Sign-aware lower endpoint evaluation of `logOnePlusRatioPoly`. -/
def logOnePlusRatioPolyLower (n : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ i ∈ range n, if Even i then lo ^ i / (i + 1) else -(hi ^ i / (i + 1))

/-- Sign-aware upper endpoint evaluation of `logOnePlusRatioPoly`. -/
def logOnePlusRatioPolyUpper (n : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ i ∈ range n, if Even i then hi ^ i / (i + 1) else -(lo ^ i / (i + 1))

/-- Pointwise Taylor enclosure for the total removable quotient
`logOnePlusRatio`. -/
theorem logOnePlusRatio_taylor_mem {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {n : ℕ} (hn : 0 < n) :
    |logOnePlusRatio u - logOnePlusRatioPoly n u| ≤ logOnePlusRatioError n u := by
  rcases hu0.eq_or_lt with rfl | hu
  · have hzero : (∑ i ∈ range n, (-1 : ℝ) ^ i * 0 ^ i / (i + 1)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro b hb hne
        simp [zero_pow hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hn)).elim
    simp [logOnePlusRatio, logOnePlusRatioPoly, logOnePlusRatioError, hzero, hn.ne']
  · simpa [logOnePlusRatio, logOnePlusRatioError, hu.ne'] using
      (log_one_add_div_taylor_mem hu hu1 n)

private theorem logOnePlusRatioPoly_mem {u lo hi : ℝ} {n : ℕ}
    (hu : u ∈ Set.Icc lo hi) (hlo : 0 ≤ lo) :
    logOnePlusRatioPolyLower n lo hi ≤ logOnePlusRatioPoly n u ∧
      logOnePlusRatioPoly n u ≤ logOnePlusRatioPolyUpper n lo hi := by
  have hu0 : 0 ≤ u := hlo.trans hu.1
  constructor
  · unfold logOnePlusRatioPolyLower logOnePlusRatioPoly
    apply Finset.sum_le_sum
    intro i hiMem
    rw [neg_one_pow_eq_ite]
    by_cases he : Even i
    · simp only [he, if_true, one_mul]
      gcongr
      exact hu.1
    · simp only [he, if_false, neg_mul]
      simpa only [one_mul, neg_div] using neg_le_neg (div_le_div_of_nonneg_right
        (c := (i : ℝ) + 1) (pow_le_pow_left₀ hu0 hu.2 i) (by positivity))
  · unfold logOnePlusRatioPolyUpper logOnePlusRatioPoly
    apply Finset.sum_le_sum
    intro i hiMem
    rw [neg_one_pow_eq_ite]
    by_cases he : Even i
    · simp only [he, if_true, one_mul]
      gcongr
      exact hu.2
    · simp only [he, if_false, neg_mul]
      simpa only [one_mul, neg_div] using neg_le_neg (div_le_div_of_nonneg_right
        (c := (i : ℝ) + 1) (pow_le_pow_left₀ hlo hu.1 i) (by positivity))

/-- Uniform enclosure of `logOnePlusRatio u` on a nonnegative interval below
the Taylor singularity at `1`. -/
theorem logOnePlusRatio_on_interval {u lo hi : ℝ} {n : ℕ}
    (hu : u ∈ Set.Icc lo hi) (hlo : 0 ≤ lo) (hhi : hi < 1) (hn : 0 < n) :
    logOnePlusRatioPolyLower n lo hi - logOnePlusRatioError n hi ≤
        logOnePlusRatio u ∧
      logOnePlusRatio u ≤
        logOnePlusRatioPolyUpper n lo hi + logOnePlusRatioError n hi := by
  have hu0 : 0 ≤ u := hlo.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt hhi
  have hmain := logOnePlusRatio_taylor_mem hu0 hu1 hn
  rw [abs_le] at hmain
  have hpoly := logOnePlusRatioPoly_mem (n := n) hu hlo
  have hpow : u ^ n ≤ hi ^ n := pow_le_pow_left₀ hu0 hu.2 n
  have hhi0 : 0 ≤ hi := hu0.trans hu.2
  have herr : logOnePlusRatioError n u ≤ logOnePlusRatioError n hi := by
    unfold logOnePlusRatioError
    have hdenU : 0 ≤ 1 - u := by linarith
    have hdenHi : 0 < 1 - hi := by linarith
    calc
      u ^ n / (1 - u) ≤ hi ^ n / (1 - u) := div_le_div_of_nonneg_right hpow hdenU
      _ ≤ hi ^ n / (1 - hi) :=
        div_le_div_of_nonneg_left (pow_nonneg hhi0 n) hdenHi (by linarith [hu.2])
  constructor <;> linarith

/-! ## The quotient `-log (1 - u) / u` -/

/-- The removable quotient `-log (1 - u) / u`, extended by `1` at zero. -/
def negLogOneSubRatio (u : ℝ) : ℝ :=
  if u = 0 then 1 else -Real.log (1 - u) / u

/-- Away from the removable singularity, `negLogOneSubRatio` is the usual
quotient. -/
theorem negLogOneSubRatio_eq_of_ne {u : ℝ} (hu : u ≠ 0) :
    negLogOneSubRatio u = -Real.log (1 - u) / u := by
  simp [negLogOneSubRatio, hu]

/-- The first `n` terms of the power series for `negLogOneSubRatio`. -/
def negLogOneSubRatioPoly (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ range n, u ^ i / (i + 1)

/-- Taylor error used for `negLogOneSubRatio`. -/
def negLogOneSubRatioError (n : ℕ) (u : ℝ) : ℝ := u ^ n / (1 - u)

/-- Pointwise Taylor enclosure for `negLogOneSubRatio`. -/
theorem negLogOneSubRatio_taylor_mem {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) {n : ℕ} (hn : 0 < n) :
    |negLogOneSubRatio u - negLogOneSubRatioPoly n u| ≤ negLogOneSubRatioError n u := by
  rcases hu0.eq_or_lt with rfl | hu
  · have hzero : (∑ i ∈ range n, (0 : ℝ) ^ i / (i + 1)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro b hb hne
        simp [zero_pow hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hn)).elim
    simp [negLogOneSubRatio, negLogOneSubRatioPoly, negLogOneSubRatioError, hzero, hn.ne']
  · have h := Real.abs_log_sub_add_sum_range_le
      (x := u) (by simpa [abs_of_pos hu] using hu1) n
    have hsum : (∑ i ∈ range n, u ^ (i + 1) / (i + 1)) =
        u * negLogOneSubRatioPoly n u := by
      rw [negLogOneSubRatioPoly, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ']
      ring
    rw [hsum] at h
    have hu' : u ≠ 0 := hu.ne'
    have h' : |-Real.log (1 - u) - u * negLogOneSubRatioPoly n u| ≤
        u * negLogOneSubRatioError n u := by
      calc
        |-Real.log (1 - u) - u * negLogOneSubRatioPoly n u| =
            |u * negLogOneSubRatioPoly n u + Real.log (1 - u)| := by
              rw [show -Real.log (1 - u) - u * negLogOneSubRatioPoly n u =
                -(u * negLogOneSubRatioPoly n u + Real.log (1 - u)) by ring, abs_neg]
        _ ≤ u ^ (n + 1) / (1 - u) := by simpa [abs_of_pos hu] using h
        _ = u * negLogOneSubRatioError n u := by
          rw [negLogOneSubRatioError, pow_succ]
          ring
    have heq : -Real.log (1 - u) / u - negLogOneSubRatioPoly n u =
        (-Real.log (1 - u) - u * negLogOneSubRatioPoly n u) / u := by field_simp [hu']
    rw [negLogOneSubRatio, if_neg hu', heq, abs_div, abs_of_pos hu, div_le_iff₀ hu]
    simpa [mul_comm] using h'

/-- Uniform enclosure of `negLogOneSubRatio u` on a nonnegative interval below
`1`. -/
theorem negLogOneSubRatio_on_interval {u lo hi : ℝ} {n : ℕ}
    (hu : u ∈ Set.Icc lo hi) (hlo : 0 ≤ lo) (hhi : hi < 1) (hn : 0 < n) :
    negLogOneSubRatioPoly n lo - negLogOneSubRatioError n hi ≤ negLogOneSubRatio u ∧
      negLogOneSubRatio u ≤ negLogOneSubRatioPoly n hi + negLogOneSubRatioError n hi := by
  have hu0 : 0 ≤ u := hlo.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt hhi
  have hmain := negLogOneSubRatio_taylor_mem hu0 hu1 hn
  rw [abs_le] at hmain
  have hpolyLo : negLogOneSubRatioPoly n lo ≤ negLogOneSubRatioPoly n u := by
    unfold negLogOneSubRatioPoly
    apply Finset.sum_le_sum
    intro i hiMem
    gcongr
    exact hu.1
  have hpolyHi : negLogOneSubRatioPoly n u ≤ negLogOneSubRatioPoly n hi := by
    unfold negLogOneSubRatioPoly
    apply Finset.sum_le_sum
    intro i hiMem
    gcongr
    exact hu.2
  have hpow : u ^ n ≤ hi ^ n := pow_le_pow_left₀ hu0 hu.2 n
  have hhi0 : 0 ≤ hi := hu0.trans hu.2
  have herr : negLogOneSubRatioError n u ≤ negLogOneSubRatioError n hi := by
    unfold negLogOneSubRatioError
    have hdenU : 0 ≤ 1 - u := by linarith
    have hdenHi : 0 < 1 - hi := by linarith
    calc
      u ^ n / (1 - u) ≤ hi ^ n / (1 - u) := div_le_div_of_nonneg_right hpow hdenU
      _ ≤ hi ^ n / (1 - hi) := by
        gcongr
        exact hu.2
  constructor <;> linarith

/-! ## The quotient `(1 - exp (-v)) / v` -/

/-- The removable quotient `(1 - exp (-v)) / v`, extended by `1` at zero. -/
def oneSubExpNegRatio (v : ℝ) : ℝ :=
  if v = 0 then 1 else (1 - Real.exp (-v)) / v

/-- Away from the removable singularity, `oneSubExpNegRatio` is the usual
quotient. -/
theorem oneSubExpNegRatio_eq_of_ne {v : ℝ} (hv : v ≠ 0) :
    oneSubExpNegRatio v = (1 - Real.exp (-v)) / v := by
  simp [oneSubExpNegRatio, hv]

/-- The first `n` terms of the alternating series for `oneSubExpNegRatio`. -/
def oneSubExpNegRatioPoly (n : ℕ) (v : ℝ) : ℝ :=
  ∑ i ∈ range n, (-1 : ℝ) ^ i * v ^ i / (i + 1).factorial

/-- A geometric majorant for the Taylor tail of `oneSubExpNegRatio`. -/
def oneSubExpNegRatioError (n : ℕ) (v : ℝ) : ℝ :=
  2 * v ^ n / (n + 1).factorial

/-- Sign-aware lower endpoint evaluation of `oneSubExpNegRatioPoly`. -/
def oneSubExpNegRatioPolyLower (n : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ i ∈ range n, if Even i then lo ^ i / (i + 1).factorial
    else -(hi ^ i / (i + 1).factorial)

/-- Sign-aware upper endpoint evaluation of `oneSubExpNegRatioPoly`. -/
def oneSubExpNegRatioPolyUpper (n : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ i ∈ range n, if Even i then hi ^ i / (i + 1).factorial
    else -(lo ^ i / (i + 1).factorial)

private theorem exp_neg_general_bound {v : ℝ} (hv : 0 ≤ v) {n : ℕ}
    (hscale : v / n.succ ≤ 1 / 2) :
    |Real.exp (-v) - ∑ m ∈ range n, (-v) ^ m / m.factorial| ≤
      v ^ n / n.factorial * 2 := by
  have hc := Complex.exp_bound'
    (x := ((-v : ℝ) : ℂ)) (n := n) (by simpa [abs_of_nonneg hv] using hscale)
  convert hc using 1 <;> norm_cast
  simp [Real.norm_eq_abs, abs_of_nonneg hv]

/-- Pointwise Taylor enclosure for `oneSubExpNegRatio`.  The scale hypothesis
allows arguments larger than one by choosing a sufficiently high degree. -/
theorem oneSubExpNegRatio_taylor_mem {v : ℝ} (hv : 0 ≤ v) {n : ℕ}
    (hn : 0 < n) (hscale : v / (n + 2) ≤ 1 / 2) :
    |oneSubExpNegRatio v - oneSubExpNegRatioPoly n v| ≤ oneSubExpNegRatioError n v := by
  rcases hv.eq_or_lt with rfl | hvpos
  · have hzero : (∑ i ∈ range n, (-1 : ℝ) ^ i * 0 ^ i / (i + 1).factorial) = 1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro b hb hne
        simp [zero_pow hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hn)).elim
    simp [oneSubExpNegRatio, oneSubExpNegRatioPoly, oneSubExpNegRatioError, hzero, hn.ne']
  · have hcast : ((n + 1).succ : ℝ) = (n : ℝ) + 2 := by
      push_cast
      ring
    have hs : v / (n + 1).succ ≤ (1 / 2 : ℝ) := by
      rw [hcast]
      exact hscale
    have h := exp_neg_general_bound hv (n := n + 1) hs
    have hsum : (∑ m ∈ range (n + 1), (-v) ^ m / m.factorial) =
        1 - v * oneSubExpNegRatioPoly n v := by
      calc
        (∑ m ∈ range (n + 1), (-v) ^ m / m.factorial) =
            1 + ∑ i ∈ range n, (-v) ^ (i + 1) / (i + 1).factorial := by
          rw [Finset.sum_range_succ']
          norm_num
          ring
        _ = 1 + ∑ i ∈ range n,
              -(v * ((-1 : ℝ) ^ i * v ^ i / (i + 1).factorial)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ, neg_pow]
          ring
        _ = 1 - v * oneSubExpNegRatioPoly n v := by
          rw [oneSubExpNegRatioPoly, Finset.mul_sum, Finset.sum_neg_distrib]
          ring
    rw [hsum] at h
    have hvne : v ≠ 0 := hvpos.ne'
    have heq : (1 - Real.exp (-v)) / v - oneSubExpNegRatioPoly n v =
        -(Real.exp (-v) - (1 - v * oneSubExpNegRatioPoly n v)) / v := by
      field_simp [hvne]
      ring
    rw [oneSubExpNegRatio, if_neg hvne, heq, abs_div, abs_neg,
      abs_of_pos hvpos, div_le_iff₀ hvpos]
    unfold oneSubExpNegRatioError
    calc
      |Real.exp (-v) - (1 - v * oneSubExpNegRatioPoly n v)| ≤
          v ^ (n + 1) / (n + 1).factorial * 2 := h
      _ = (2 * v ^ n / (n + 1).factorial) * v := by
        rw [pow_succ]
        ring

private theorem oneSubExpNegRatioPoly_mem {v lo hi : ℝ} {n : ℕ}
    (hv : v ∈ Set.Icc lo hi) (hlo : 0 ≤ lo) :
    oneSubExpNegRatioPolyLower n lo hi ≤ oneSubExpNegRatioPoly n v ∧
      oneSubExpNegRatioPoly n v ≤ oneSubExpNegRatioPolyUpper n lo hi := by
  have hv0 : 0 ≤ v := hlo.trans hv.1
  constructor
  · unfold oneSubExpNegRatioPolyLower oneSubExpNegRatioPoly
    apply Finset.sum_le_sum
    intro i hiMem
    rw [neg_one_pow_eq_ite]
    by_cases he : Even i
    · simp only [he, if_true, one_mul]
      gcongr
      exact hv.1
    · simp only [he, if_false, neg_mul]
      simpa only [one_mul, neg_div] using neg_le_neg (div_le_div_of_nonneg_right
        (c := ((i + 1).factorial : ℝ)) (pow_le_pow_left₀ hv0 hv.2 i) (by positivity))
  · unfold oneSubExpNegRatioPolyUpper oneSubExpNegRatioPoly
    apply Finset.sum_le_sum
    intro i hiMem
    rw [neg_one_pow_eq_ite]
    by_cases he : Even i
    · simp only [he, if_true, one_mul]
      gcongr
      exact hv.2
    · simp only [he, if_false, neg_mul]
      simpa only [one_mul, neg_div] using neg_le_neg (div_le_div_of_nonneg_right
        (c := ((i + 1).factorial : ℝ)) (pow_le_pow_left₀ hlo hv.1 i) (by positivity))

/-- Uniform enclosure of `oneSubExpNegRatio v` on a nonnegative interval. -/
theorem oneSubExpNegRatio_on_interval {v lo hi : ℝ} {n : ℕ}
    (hv : v ∈ Set.Icc lo hi) (hlo : 0 ≤ lo) (hn : 0 < n)
    (hscale : hi / (n + 2) ≤ 1 / 2) :
    oneSubExpNegRatioPolyLower n lo hi - oneSubExpNegRatioError n hi ≤
        oneSubExpNegRatio v ∧
      oneSubExpNegRatio v ≤
        oneSubExpNegRatioPolyUpper n lo hi + oneSubExpNegRatioError n hi := by
  have hv0 : 0 ≤ v := hlo.trans hv.1
  have hvscale : v / (n + 2) ≤ (1 / 2 : ℝ) :=
    (div_le_div_of_nonneg_right hv.2 (by positivity)).trans hscale
  have hmain := oneSubExpNegRatio_taylor_mem hv0 hn hvscale
  rw [abs_le] at hmain
  have hpoly := oneSubExpNegRatioPoly_mem (n := n) hv hlo
  have herr : oneSubExpNegRatioError n v ≤ oneSubExpNegRatioError n hi := by
    unfold oneSubExpNegRatioError
    gcongr
    exact hv.2
  constructor <;> linarith

end

end RamseyLean.CertifiedNumerics






