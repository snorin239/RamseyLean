import RamseyLean.Numerics.FinalCertificateData.CrossingFineAChunk000
import RamseyLean.Numerics.FinalCertificateData.CrossingFineAChunk001
import RamseyLean.Numerics.FinalCertificateData.CrossingFineAChunk002
import RamseyLean.Numerics.FinalCertificateData.CrossingFineAChunk003

/-! Aggregated checked rows for the `CrossingFineA` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def crossingFineAPairs : List (Interval × CrossingData) :=
  CrossingFineAChunk000.pairs ++
    CrossingFineAChunk001.pairs ++
    CrossingFineAChunk002.pairs ++
    CrossingFineAChunk003.pairs

theorem crossingFineAChecks_true :
    crossingFineAPairs.all (crossingPairCheck) = true := by
  have h000 : CrossingFineAChunk000.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineAChunk000.checks] using CrossingFineAChunk000.checks_true
  have h001 : CrossingFineAChunk001.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineAChunk001.checks] using CrossingFineAChunk001.checks_true
  have h002 : CrossingFineAChunk002.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineAChunk002.checks] using CrossingFineAChunk002.checks_true
  have h003 : CrossingFineAChunk003.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingFineAChunk003.checks] using CrossingFineAChunk003.checks_true
  simpa only [crossingFineAPairs, List.all_append, h000, h001, h002, h003,
    Bool.and_self]

def crossingFineAInputs : List Interval :=
  List.range 100 |>.map (uniformCell (360000000000) (10000000))

set_option maxHeartbeats 0 in
theorem crossingFineAMap_fst :
    crossingFineAPairs.map Prod.fst = crossingFineAInputs := by
  have h000 : CrossingFineAChunk000.pairs.map Prod.fst = CrossingFineAChunk000.inputs :=
    CrossingFineAChunk000.map_fst
  have h001 : CrossingFineAChunk001.pairs.map Prod.fst = CrossingFineAChunk001.inputs :=
    CrossingFineAChunk001.map_fst
  have h002 : CrossingFineAChunk002.pairs.map Prod.fst = CrossingFineAChunk002.inputs :=
    CrossingFineAChunk002.map_fst
  have h003 : CrossingFineAChunk003.pairs.map Prod.fst = CrossingFineAChunk003.inputs :=
    CrossingFineAChunk003.map_fst
  simp only [crossingFineAPairs, List.map_append, h000, h001, h002, h003]
  decide

theorem exists_checked_crossingFineA (k : ℕ) (hk : k < 100) :
    ∃ d : CrossingData, d.input = uniformCell (360000000000) (10000000) k ∧
      crossingCheck d = true := by
  have hmemRange : k ∈ List.range 100 := List.mem_range.mpr hk
  have hmem : uniformCell (360000000000) (10000000) k ∈ crossingFineAInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst crossingFineAMap_fst crossingFineAChecks_true hmem with
    ⟨d, hd⟩
  simp only [crossingPairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
