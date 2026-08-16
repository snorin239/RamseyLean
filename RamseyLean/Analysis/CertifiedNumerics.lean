import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Kernel-checked elementary numerical bounds

This module provides a small certificate layer for rigorous numerical work with
`Real.exp` and `Real.log`.  Its soundness rests on Mathlib's proved Taylor
remainder estimates.  Once the Taylor degree and rational interval endpoints
are fixed, the remaining certificate obligations are exact rational or
polynomial inequalities suitable for `norm_num`, `linarith`, and `nlinarith`.

The definitions here are generic infrastructure for the independent numerical
optimization used in paper Lemma `lem:numerics`; they do not encode or trust
the manuscript's external computer-algebra output.
-/

set_option autoImplicit false

namespace RamseyLean.CertifiedNumerics

open Finset

/-- The degree-`n - 1` Taylor polynomial for the real exponential at zero. -/
noncomputable def expPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ range n, x ^ m / m.factorial

/-- Mathlib's explicit error majorant for `expPoly` on `[-1, 1]`. -/
noncomputable def expError (n : ℕ) (x : ℝ) : ℝ :=
  |x| ^ n * (n.succ / (n.factorial * n))

/-- The first `n` terms of the odd series for
`(1 / 2) * log ((1 + z) / (1 - z))`. -/
noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)

/-- Mathlib's explicit error majorant for `logSeries` on `(-1, 1)`. -/
noncomputable def logError (n : ℕ) (z : ℝ) : ℝ :=
  |z| ^ (2 * n + 1) / (1 - z ^ 2)

/-- The kernel-checked exponential Taylor estimate, in directly usable
two-sided form. -/
theorem exp_taylor_mem {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    expPoly n x - expError n x ≤ Real.exp x ∧
      Real.exp x ≤ expPoly n x + expError n x := by
  have h := Real.exp_bound hx hn
  simp only [expPoly, expError]
  constructor <;>
    linarith [neg_abs_le (Real.exp x - ∑ m ∈ range n, x ^ m / m.factorial),
      le_abs_self (Real.exp x - ∑ m ∈ range n, x ^ m / m.factorial)]

/-- Lift rational endpoint Taylor certificates to an enclosure of `exp x` on
an entire interval. -/
theorem exp_on_interval {x a b lo hi : ℝ} {n : ℕ}
    (hx : x ∈ Set.Icc a b) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hn : 0 < n)
    (hlo : lo ≤ expPoly n a - expError n a)
    (hhi : expPoly n b + expError n b ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have hta := exp_taylor_mem ha hn
  have htb := exp_taylor_mem hb hn
  exact ⟨hlo.trans (hta.1.trans (Real.exp_monotone hx.1)),
    (Real.exp_monotone hx.2).trans (htb.2.trans hhi)⟩

/-- A rational two-sided Taylor enclosure of `log q` for every positive `q`.
The change of variables `z = (q - 1) / (q + 1)` always lies in `(-1, 1)`. -/
theorem log_taylor_mem {q : ℝ} (hq : 0 < q) (n : ℕ) :
    let z := (q - 1) / (q + 1)
    2 * (logSeries n z - logError n z) ≤ Real.log q ∧
      Real.log q ≤ 2 * (logSeries n z + logError n z) := by
  let z := (q - 1) / (q + 1)
  have hden : 0 < q + 1 := by linarith
  have hzlo : -1 < z := by
    dsimp [z]
    rw [lt_div_iff₀ hden]
    linarith
  have hzhi : z < 1 := by
    dsimp [z]
    rw [div_lt_iff₀ hden]
    linarith
  have hz : |z| < 1 := (abs_lt).2 ⟨hzlo, hzhi⟩
  have hratio : (1 + z) / (1 - z) = q := by
    dsimp [z]
    field_simp [ne_of_gt hden, ne_of_gt hq]
    ring
  have h := Real.sum_range_sub_log_div_le hz n
  rw [hratio] at h
  simp only [logSeries, logError]
  constructor <;>
    linarith [neg_abs_le
      (1 / 2 * Real.log q - ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)),
      le_abs_self
      (1 / 2 * Real.log q - ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1))]

/-- Lift rational endpoint Taylor certificates to an enclosure of `log x` on
an entire positive interval. -/
theorem log_on_interval {x a b lo hi : ℝ} {n : ℕ}
    (hx : x ∈ Set.Icc a b) (ha : 0 < a)
    (hlo : lo ≤ 2 * (logSeries n ((a - 1) / (a + 1)) -
      logError n ((a - 1) / (a + 1))))
    (hhi : 2 * (logSeries n ((b - 1) / (b + 1)) +
      logError n ((b - 1) / (b + 1))) ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi := by
  have hxp : 0 < x := ha.trans_le hx.1
  have hb : 0 < b := hxp.trans_le hx.2
  have hta := log_taylor_mem ha n
  have htb := log_taylor_mem hb n
  have hax : Real.log a ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn ha hxp hx.1
  have hxb : Real.log x ≤ Real.log b :=
    Real.strictMonoOn_log.monotoneOn hxp hb hx.2
  exact ⟨hlo.trans (hta.1.trans hax), hxb.trans (htb.2.trans hhi)⟩

/-- The alternating Taylor polynomial for the removable quotient
`log (1 + u) / u`. -/
noncomputable def logOnePlusRatioPoly (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ range n, (-1 : ℝ) ^ i * u ^ i / (i + 1)

/-- A uniform enclosure of the removable quotient `log (1 + u) / u`.  Unlike
dividing a fixed log error by `u`, its error remains controlled as `u → 0+`. -/
theorem log_one_add_div_taylor_mem {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (n : ℕ) :
    |Real.log (1 + u) / u - logOnePlusRatioPoly n u| ≤ u ^ n / (1 - u) := by
  have habs : |(-u)| < 1 := by simpa [abs_of_pos hu0] using hu1
  have h := Real.abs_log_sub_add_sum_range_le habs n
  have hsum : (∑ i ∈ range n, (-u) ^ (i + 1) / (i + 1)) =
      -u * logOnePlusRatioPoly n u := by
    rw [logOnePlusRatioPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ, neg_pow]
    ring
  rw [hsum] at h
  have hu : u ≠ 0 := hu0.ne'
  rw [show 1 - -u = 1 + u by ring, abs_neg, abs_of_pos hu0, pow_succ'] at h
  have h' : |Real.log (1 + u) - u * logOnePlusRatioPoly n u| ≤
      u * (u ^ n / (1 - u)) := by
    convert h using 1 <;> ring_nf
  have heq : Real.log (1 + u) / u - logOnePlusRatioPoly n u =
      (Real.log (1 + u) - u * logOnePlusRatioPoly n u) / u := by
    field_simp [hu]
  rw [heq, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
  simpa [mul_comm] using h'

end RamseyLean.CertifiedNumerics
