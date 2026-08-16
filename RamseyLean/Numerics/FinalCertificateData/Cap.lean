import RamseyLean.Numerics.FinalCertificateData.CapChunk000

/-! Aggregated checked rows for the `Cap` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def capPairs : List (Interval × LargeData) :=
  CapChunk000.pairs

theorem capChecks_true :
    capPairs.all (capPairCheck) = true := by
  have h000 : CapChunk000.pairs.all (capPairCheck) = true := by
    simpa only [CapChunk000.checks] using CapChunk000.checks_true
  simpa only [capPairs, List.all_append, h000,
    Bool.and_self]

def capInputs : List Interval :=
  List.range 3 |>.map (uniformCell (360400000000) (200000000))

set_option maxHeartbeats 0 in
theorem capMap_fst :
    capPairs.map Prod.fst = capInputs := by
  have h000 : CapChunk000.pairs.map Prod.fst = CapChunk000.inputs :=
    CapChunk000.map_fst
  simp only [capPairs, List.map_append, h000]
  decide

theorem exists_checked_cap (k : ℕ) (hk : k < 3) :
    ∃ d : LargeData, d.input = uniformCell (360400000000) (200000000) k ∧
      capCheck d = true := by
  have hmemRange : k ∈ List.range 3 := List.mem_range.mpr hk
  have hmem : uniformCell (360400000000) (200000000) k ∈ capInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst capMap_fst capChecks_true hmem with
    ⟨d, hd⟩
  simp only [capPairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
