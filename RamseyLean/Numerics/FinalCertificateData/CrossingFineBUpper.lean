import RamseyLean.Numerics.FinalCertificateData.CrossingFineBUpperChunk000

/-! Aggregated checked rows for the `CrossingFineBUpper` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def crossingFineBUpperPairs : List (Interval × CrossingData) :=
  CrossingFineBUpperChunk000.pairs

theorem crossingFineBUpperChecks_true :
    crossingFineBUpperPairs.all (crossingPairCheck) = true := by
  have h000 : CrossingFineBUpperChunk000.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineBUpperChunk000.checks] using CrossingFineBUpperChunk000.checks_true
  simpa only [crossingFineBUpperPairs, List.all_append, h000,
    Bool.and_self]

def crossingFineBUpperInputs : List Interval :=
  List.range 10 |>.map (uniformCell (258000000000) (100000000))

set_option maxHeartbeats 0 in
theorem crossingFineBUpperMap_fst :
    crossingFineBUpperPairs.map Prod.fst = crossingFineBUpperInputs := by
  have h000 : CrossingFineBUpperChunk000.pairs.map Prod.fst = CrossingFineBUpperChunk000.inputs :=
    CrossingFineBUpperChunk000.map_fst
  simp only [crossingFineBUpperPairs, List.map_append, h000]
  decide

theorem exists_checked_crossingFineBUpper (k : ℕ) (hk : k < 10) :
    ∃ d : CrossingData, d.input = uniformCell (258000000000) (100000000) k ∧
      crossingCheck d = true := by
  have hmemRange : k ∈ List.range 10 := List.mem_range.mpr hk
  have hmem : uniformCell (258000000000) (100000000) k ∈ crossingFineBUpperInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst crossingFineBUpperMap_fst crossingFineBUpperChecks_true hmem with
    ⟨d, hd⟩
  simp only [crossingPairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
