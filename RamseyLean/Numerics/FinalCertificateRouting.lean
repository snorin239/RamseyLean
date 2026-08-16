import RamseyLean.Numerics.FinalCertificateAssembly

/-!
# Routing the generated final-certificate rows

This module states the small interface supplied by the generated data
aggregator and turns it into the continuum package used by the final
certificate assembly.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

/-- Existence of a checked literal row for every cell of every fixed mesh. -/
structure FinalRowCertificate : Prop where
  smallSeries : ∀ k : ℕ, k < 500 → ∃ d : SmallCoordinateData,
    d.small.input = uniformCell 0 200000000 k ∧
      d.small.band = .zeroTenth ∧ smallCoordinateCheck d = true
  smallQuotientA : ∀ k : ℕ, k < 1000 →
    ∃ d : SmallCoordinateQuotientData,
      d.small.input = uniformCell 100000000000 100000000 k ∧
        d.small.band = .tenthFifth ∧
          smallCoordinateQuotientCheck d = true
  smallQuotientB : ∀ k : ℕ, k < 580 →
    ∃ d : SmallCoordinateQuotientData,
      d.small.input = uniformCell 200000000000 100000000 k ∧
        d.small.band = .fifthCut ∧
          smallCoordinateQuotientCheck d = true
  middle : ∀ k : ℕ, k < 514 → ∃ d : MiddleData,
    d.input = uniformCell 257800000000 200000000 k ∧ middleCheck d = true
  cap : ∀ k : ℕ, k < 3 → ∃ d : LargeData,
    d.input = uniformCell 360400000000 200000000 k ∧ capCheck d = true
  large0 : ∀ k : ℕ, k < 228 → ∃ d : LargeData,
    d.input = uniformCell 361000000000 50000000 k ∧
      largeCheck .cutNineTwentieths d = true
  large1 : ∀ k : ℕ, k < 776 → ∃ d : LargeData,
    d.input = uniformCell 372400000000 100000000 k ∧
      largeCheck .cutNineTwentieths d = true
  large2 : ∀ k : ℕ, k < 1500 → ∃ d : LargeData,
    d.input = uniformCell 450000000000 100000000 k ∧
      largeCheck .nineTwentiethsThreeFifths d = true
  large3 : ∀ k : ℕ, k < 4000 → ∃ d : LargeData,
    d.input = uniformCell 600000000000 100000000 k ∧
      largeCheck .threeFifthsOne d = true
  crossingCoarse : ∀ k : ℕ, k < 1000 → k ≠ 257 → k ≠ 258 →
    k ≠ 359 → k ≠ 360 →
    ∃ d : CrossingData,
      d.input = uniformCell 0 1000000000 k ∧ crossingCheck d = true
  crossingFineB : ∀ k : ℕ, k < 10 → ∃ d : CrossingData,
    d.input = uniformCell 257000000000 100000000 k ∧
      crossingCheck d = true
  crossingFineBUpper : ∀ k : ℕ, k < 10 → ∃ d : CrossingData,
    d.input = uniformCell 258000000000 100000000 k ∧
      crossingCheck d = true
  crossingFineALower : ∀ k : ℕ, k < 10 → ∃ d : CrossingData,
    d.input = uniformCell 359000000000 100000000 k ∧
      crossingCheck d = true
  crossingFineA : ∀ k : ℕ, k < 100 → ∃ d : CrossingData,
    d.input = uniformCell 360000000000 10000000 k ∧
      crossingCheck d = true

private theorem coarse_suffix
    (h : FinalRowCertificate) (offset N : ℕ)
    (hbound : offset + N ≤ 1000) (h257 : 257 ∉ Set.Ico offset (offset + N))
    (h258 : 258 ∉ Set.Ico offset (offset + N))
    (h359 : 359 ∉ Set.Ico offset (offset + N))
    (h360 : 360 ∉ Set.Ico offset (offset + N)) :
    ∀ k : ℕ, k < N → ∃ d : CrossingData,
      d.input = uniformCell (1000000000 * offset) 1000000000 k ∧
        crossingCheck d = true := by
  intro k hk
  have hglobal : offset + k < 1000 := by omega
  have hn257 : offset + k ≠ 257 := by
    intro heq
    apply h257
    constructor <;> omega
  have hn258 : offset + k ≠ 258 := by
    intro heq
    apply h258
    constructor <;> omega
  have hn359 : offset + k ≠ 359 := by
    intro heq
    apply h359
    constructor <;> omega
  have hn360 : offset + k ≠ 360 := by
    intro heq
    apply h360
    constructor <;> omega
  obtain ⟨d, hinput, hcheck⟩ :=
    h.crossingCoarse (offset + k) hglobal hn257 hn258 hn359 hn360
  refine ⟨d, ?_, hcheck⟩
  rw [hinput]
  simpa only [zero_add] using
    (uniformCell_shift 0 1000000000 offset k).symm

private theorem fineA_suffix
    (h : FinalRowCertificate) (offset N : ℕ) (hbound : offset + N ≤ 100) :
    ∀ k : ℕ, k < N → ∃ d : CrossingData,
      d.input =
        uniformCell (360000000000 + 10000000 * offset) 10000000 k ∧
        crossingCheck d = true := by
  intro k hk
  obtain ⟨d, hinput, hcheck⟩ := h.crossingFineA (offset + k) (by omega)
  refine ⟨d, ?_, hcheck⟩
  rw [hinput]
  exact (uniformCell_shift 360000000000 10000000 offset k).symm

/-- The generated checked rows cover every continuum obligation. -/
theorem finalContinuumCertificate_of_rows
    (h : FinalRowCertificate) : FinalContinuumCertificate := by
  refine
    { small := ?_
      middle := ?_
      cap := ?_
      large := ?_
      bBelow := ?_
      bAbove := ?_
      aBelow := ?_
      aAbove := ?_ }
  · intro r hr hrCut
    by_cases h0 : r ≤ (1 / 10 : ℝ)
    · apply small_on_uniform_band (N := 500) (band := .zeroTenth)
        (by norm_num) (by norm_num) h.smallSeries (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith [hr.1]
      · change r ≤ (1 / 10 : ℝ)
        exact h0
    by_cases h1 : r ≤ (1 / 5 : ℝ)
    · apply small_quotient_on_uniform_band (N := 1000)
        (band := .tenthFifth) (by norm_num) (by norm_num)
        h.smallQuotientA (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith
      · change (1 / 10 : ℝ) < r ∧ r ≤ 1 / 5
        exact ⟨lt_of_not_ge h0, h1⟩
    · apply small_quotient_on_uniform_band (N := 580)
        (band := .fifthCut) (by norm_num) (by norm_num)
        h.smallQuotientB (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith
      · change (1 / 5 : ℝ) < r
        exact lt_of_not_ge h1
  · intro r hr hlo hhi
    apply middle_pos_on_uniform_band (N := 514)
      (by norm_num) (by norm_num) h.middle (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  · intro r hr hlo hhi
    apply cap_pos_on_uniform_band (N := 3)
      (by norm_num) (by norm_num) h.cap (hr := hr)
    constructor <;> norm_num [value, scale] <;> linarith
  · intro r hr hcut
    by_cases h0 : r ≤ (3724 / 10000 : ℝ)
    · apply large_on_uniform_band (N := 228)
        (band := .cutNineTwentieths) (by norm_num) (by norm_num)
        h.large0 (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith
      · change r ≤ (9 / 20 : ℝ)
        linarith
    by_cases h1 : r ≤ (9 / 20 : ℝ)
    · apply large_on_uniform_band (N := 776)
        (band := .cutNineTwentieths) (by norm_num) (by norm_num)
        h.large1 (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith
      · exact h1
    by_cases h2 : r ≤ (3 / 5 : ℝ)
    · apply large_on_uniform_band (N := 1500)
        (band := .nineTwentiethsThreeFifths)
        (by norm_num) (by norm_num) h.large2 (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith
      · exact ⟨lt_of_not_ge h1, h2⟩
    · apply large_on_uniform_band (N := 4000)
        (band := .threeFifthsOne) (by norm_num) (by norm_num)
        h.large3 (hr := hr)
      · constructor <;> norm_num [value, scale] <;> linarith [hr.2]
      · exact lt_of_not_ge h2
  · intro r hr hcut
    by_cases h0 : r ≤ (257 / 1000 : ℝ)
    · apply crossing_bBelow_on_uniform_band (N := 257)
        (by norm_num) (by norm_num)
        (coarse_suffix h 0 257 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num))
        (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith [hr.1]
    · apply crossing_bBelow_on_uniform_band (N := 8)
        (by norm_num) (by norm_num)
        (fun k hk => h.crossingFineB k (by omega)) (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
  · intro r hr hlo
    by_cases h0 : r ≤ (259 / 1000 : ℝ)
    · apply crossing_bAbove_on_uniform_band (N := 10)
        (by norm_num) (by norm_num)
        h.crossingFineBUpper
        (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
    by_cases h1 : r ≤ (359 / 1000 : ℝ)
    · apply crossing_bAbove_on_uniform_band (N := 100)
        (by norm_num) (by norm_num)
        (coarse_suffix h 259 100 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num))
        (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
    by_cases h2 : r ≤ (360 / 1000 : ℝ)
    · apply crossing_bAbove_on_uniform_band (N := 10)
        (by norm_num) (by norm_num) h.crossingFineALower (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
    by_cases h3 : r ≤ (361 / 1000 : ℝ)
    · apply crossing_bAbove_on_uniform_band (N := 100)
        (by norm_num) (by norm_num) h.crossingFineA (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
    · apply crossing_bAbove_on_uniform_band (N := 639)
        (by norm_num) (by norm_num)
        (coarse_suffix h 361 639 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num))
        (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith [hr.2]
  · intro r hr hhi
    by_cases h0 : r ≤ (257 / 1000 : ℝ)
    · apply crossing_aBelow_on_uniform_band (N := 257)
        (by norm_num) (by norm_num)
        (coarse_suffix h 0 257 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num))
        (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith [hr.1]
    by_cases h1 : r ≤ (258 / 1000 : ℝ)
    · apply crossing_aBelow_on_uniform_band (N := 10)
        (by norm_num) (by norm_num) h.crossingFineB (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
    by_cases h2 : r ≤ (360 / 1000 : ℝ)
    · by_cases h3 : r ≤ (259 / 1000 : ℝ)
      · apply crossing_aBelow_on_uniform_band (N := 10)
          (by norm_num) (by norm_num) h.crossingFineBUpper (hr := hr)
        · intro k hk
          simp only [uniformCell]
          omega
        · constructor <;> norm_num [value, scale] <;> linarith
      by_cases h4 : r ≤ (359 / 1000 : ℝ)
      · apply crossing_aBelow_on_uniform_band (N := 100)
          (by norm_num) (by norm_num)
          (coarse_suffix h 259 100 (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num))
          (hr := hr)
        · intro k hk
          simp only [uniformCell]
          omega
        · constructor <;> norm_num [value, scale] <;> linarith
      · apply crossing_aBelow_on_uniform_band (N := 10)
          (by norm_num) (by norm_num) h.crossingFineALower (hr := hr)
        · intro k hk
          simp only [uniformCell]
          omega
        · constructor <;> norm_num [value, scale] <;> linarith
    · apply crossing_aBelow_on_uniform_band (N := 40)
        (by norm_num) (by norm_num)
        (fun k hk => h.crossingFineA k (by omega)) (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
  · intro r hr hlo
    by_cases h0 : r ≤ (361 / 1000 : ℝ)
    · apply crossing_aAbove_on_uniform_band (N := 50)
        (by norm_num) (by norm_num)
        (fineA_suffix h 50 50 (by norm_num)) (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith
    · apply crossing_aAbove_on_uniform_band (N := 639)
        (by norm_num) (by norm_num)
        (coarse_suffix h 361 639 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num))
        (hr := hr)
      · intro k hk
        simp only [uniformCell]
        omega
      · constructor <;> norm_num [value, scale] <;> linarith [hr.2]

/-- A complete collection of checked rows yields the final numerical
certificate used by the descent theorem. -/
theorem finalNumericalCertificate_of_rows
    (h : FinalRowCertificate) : FinalNumericalCertificate :=
  finalNumericalCertificate_of_continuum
    (finalContinuumCertificate_of_rows h)

end

end RamseyLean.FinalCertificate
