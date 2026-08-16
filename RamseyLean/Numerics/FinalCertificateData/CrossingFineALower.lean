import RamseyLean.Numerics.FinalCertificateData.CrossingFineALowerChunk000

/-! Aggregated checked rows for the `CrossingFineALower` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def crossingFineALowerPairs : List (Interval × CrossingData) :=
  CrossingFineALowerChunk000.pairs

theorem crossingFineALowerChecks_true :
    crossingFineALowerPairs.all (crossingPairCheck) = true := by
  have h000 : CrossingFineALowerChunk000.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineALowerChunk000.checks] using CrossingFineALowerChunk000.checks_true
  simpa only [crossingFineALowerPairs, List.all_append, h000,
    Bool.and_self]

def crossingFineALowerInputs : List Interval :=
  List.range 10 |>.map (uniformCell (359000000000) (100000000))

set_option maxHeartbeats 0 in
theorem crossingFineALowerMap_fst :
    crossingFineALowerPairs.map Prod.fst = crossingFineALowerInputs := by
  have h000 : CrossingFineALowerChunk000.pairs.map Prod.fst = CrossingFineALowerChunk000.inputs :=
    CrossingFineALowerChunk000.map_fst
  simp only [crossingFineALowerPairs, List.map_append, h000]
  decide

theorem exists_checked_crossingFineALower (k : ℕ) (hk : k < 10) :
    ∃ d : CrossingData, d.input = uniformCell (359000000000) (100000000) k ∧
      crossingCheck d = true := by
  have hmemRange : k ∈ List.range 10 := List.mem_range.mpr hk
  have hmem : uniformCell (359000000000) (100000000) k ∈ crossingFineALowerInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst crossingFineALowerMap_fst crossingFineALowerChecks_true hmem with
    ⟨d, hd⟩
  simp only [crossingPairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
