import RamseyLean.Numerics.FinalCertificateData.CrossingFineBChunk000

/-! Aggregated checked rows for the `CrossingFineB` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def crossingFineBPairs : List (Interval × CrossingData) :=
  CrossingFineBChunk000.pairs

theorem crossingFineBChecks_true :
    crossingFineBPairs.all (crossingPairCheck) = true := by
  have h000 : CrossingFineBChunk000.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineBChunk000.checks] using CrossingFineBChunk000.checks_true
  simpa only [crossingFineBPairs, List.all_append, h000,
    Bool.and_self]

def crossingFineBInputs : List Interval :=
  List.range 10 |>.map (uniformCell (257000000000) (100000000))

set_option maxHeartbeats 0 in
theorem crossingFineBMap_fst :
    crossingFineBPairs.map Prod.fst = crossingFineBInputs := by
  have h000 : CrossingFineBChunk000.pairs.map Prod.fst = CrossingFineBChunk000.inputs :=
    CrossingFineBChunk000.map_fst
  simp only [crossingFineBPairs, List.map_append, h000]
  decide

theorem exists_checked_crossingFineB (k : ℕ) (hk : k < 10) :
    ∃ d : CrossingData, d.input = uniformCell (257000000000) (100000000) k ∧
      crossingCheck d = true := by
  have hmemRange : k ∈ List.range 10 := List.mem_range.mpr hk
  have hmem : uniformCell (257000000000) (100000000) k ∈ crossingFineBInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst crossingFineBMap_fst crossingFineBChecks_true hmem with
    ⟨d, hd⟩
  simp only [crossingPairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
