import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk000
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk001
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk002
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk003
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk004
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk005
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk006
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk007
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk008
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk009
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk010
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk011
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk012
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk013
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk014
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk015
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk016
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk017
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk018
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk019
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk020
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk021
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk022
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk023
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk024
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk025
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk026
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk027
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk028
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk029
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk030
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk031
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk032
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk033
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk034
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk035
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk036
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk037
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk038
import RamseyLean.Numerics.FinalCertificateData.CrossingCoarseChunk039

/-! Aggregated checked rows for the `CrossingCoarse` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def crossingCoarsePairs : List (Interval × CrossingData) :=
  CrossingCoarseChunk000.pairs ++
    CrossingCoarseChunk001.pairs ++
    CrossingCoarseChunk002.pairs ++
    CrossingCoarseChunk003.pairs ++
    CrossingCoarseChunk004.pairs ++
    CrossingCoarseChunk005.pairs ++
    CrossingCoarseChunk006.pairs ++
    CrossingCoarseChunk007.pairs ++
    CrossingCoarseChunk008.pairs ++
    CrossingCoarseChunk009.pairs ++
    CrossingCoarseChunk010.pairs ++
    CrossingCoarseChunk011.pairs ++
    CrossingCoarseChunk012.pairs ++
    CrossingCoarseChunk013.pairs ++
    CrossingCoarseChunk014.pairs ++
    CrossingCoarseChunk015.pairs ++
    CrossingCoarseChunk016.pairs ++
    CrossingCoarseChunk017.pairs ++
    CrossingCoarseChunk018.pairs ++
    CrossingCoarseChunk019.pairs ++
    CrossingCoarseChunk020.pairs ++
    CrossingCoarseChunk021.pairs ++
    CrossingCoarseChunk022.pairs ++
    CrossingCoarseChunk023.pairs ++
    CrossingCoarseChunk024.pairs ++
    CrossingCoarseChunk025.pairs ++
    CrossingCoarseChunk026.pairs ++
    CrossingCoarseChunk027.pairs ++
    CrossingCoarseChunk028.pairs ++
    CrossingCoarseChunk029.pairs ++
    CrossingCoarseChunk030.pairs ++
    CrossingCoarseChunk031.pairs ++
    CrossingCoarseChunk032.pairs ++
    CrossingCoarseChunk033.pairs ++
    CrossingCoarseChunk034.pairs ++
    CrossingCoarseChunk035.pairs ++
    CrossingCoarseChunk036.pairs ++
    CrossingCoarseChunk037.pairs ++
    CrossingCoarseChunk038.pairs ++
    CrossingCoarseChunk039.pairs

theorem crossingCoarseChecks_true :
    crossingCoarsePairs.all (crossingPairCheck) = true := by
  have h000 : CrossingCoarseChunk000.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk000.checks] using CrossingCoarseChunk000.checks_true
  have h001 : CrossingCoarseChunk001.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk001.checks] using CrossingCoarseChunk001.checks_true
  have h002 : CrossingCoarseChunk002.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk002.checks] using CrossingCoarseChunk002.checks_true
  have h003 : CrossingCoarseChunk003.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk003.checks] using CrossingCoarseChunk003.checks_true
  have h004 : CrossingCoarseChunk004.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk004.checks] using CrossingCoarseChunk004.checks_true
  have h005 : CrossingCoarseChunk005.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk005.checks] using CrossingCoarseChunk005.checks_true
  have h006 : CrossingCoarseChunk006.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk006.checks] using CrossingCoarseChunk006.checks_true
  have h007 : CrossingCoarseChunk007.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk007.checks] using CrossingCoarseChunk007.checks_true
  have h008 : CrossingCoarseChunk008.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk008.checks] using CrossingCoarseChunk008.checks_true
  have h009 : CrossingCoarseChunk009.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk009.checks] using CrossingCoarseChunk009.checks_true
  have h010 : CrossingCoarseChunk010.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk010.checks] using CrossingCoarseChunk010.checks_true
  have h011 : CrossingCoarseChunk011.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk011.checks] using CrossingCoarseChunk011.checks_true
  have h012 : CrossingCoarseChunk012.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk012.checks] using CrossingCoarseChunk012.checks_true
  have h013 : CrossingCoarseChunk013.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk013.checks] using CrossingCoarseChunk013.checks_true
  have h014 : CrossingCoarseChunk014.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk014.checks] using CrossingCoarseChunk014.checks_true
  have h015 : CrossingCoarseChunk015.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk015.checks] using CrossingCoarseChunk015.checks_true
  have h016 : CrossingCoarseChunk016.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk016.checks] using CrossingCoarseChunk016.checks_true
  have h017 : CrossingCoarseChunk017.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk017.checks] using CrossingCoarseChunk017.checks_true
  have h018 : CrossingCoarseChunk018.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk018.checks] using CrossingCoarseChunk018.checks_true
  have h019 : CrossingCoarseChunk019.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk019.checks] using CrossingCoarseChunk019.checks_true
  have h020 : CrossingCoarseChunk020.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk020.checks] using CrossingCoarseChunk020.checks_true
  have h021 : CrossingCoarseChunk021.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk021.checks] using CrossingCoarseChunk021.checks_true
  have h022 : CrossingCoarseChunk022.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk022.checks] using CrossingCoarseChunk022.checks_true
  have h023 : CrossingCoarseChunk023.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk023.checks] using CrossingCoarseChunk023.checks_true
  have h024 : CrossingCoarseChunk024.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk024.checks] using CrossingCoarseChunk024.checks_true
  have h025 : CrossingCoarseChunk025.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk025.checks] using CrossingCoarseChunk025.checks_true
  have h026 : CrossingCoarseChunk026.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk026.checks] using CrossingCoarseChunk026.checks_true
  have h027 : CrossingCoarseChunk027.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk027.checks] using CrossingCoarseChunk027.checks_true
  have h028 : CrossingCoarseChunk028.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk028.checks] using CrossingCoarseChunk028.checks_true
  have h029 : CrossingCoarseChunk029.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk029.checks] using CrossingCoarseChunk029.checks_true
  have h030 : CrossingCoarseChunk030.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk030.checks] using CrossingCoarseChunk030.checks_true
  have h031 : CrossingCoarseChunk031.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk031.checks] using CrossingCoarseChunk031.checks_true
  have h032 : CrossingCoarseChunk032.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk032.checks] using CrossingCoarseChunk032.checks_true
  have h033 : CrossingCoarseChunk033.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk033.checks] using CrossingCoarseChunk033.checks_true
  have h034 : CrossingCoarseChunk034.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk034.checks] using CrossingCoarseChunk034.checks_true
  have h035 : CrossingCoarseChunk035.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk035.checks] using CrossingCoarseChunk035.checks_true
  have h036 : CrossingCoarseChunk036.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk036.checks] using CrossingCoarseChunk036.checks_true
  have h037 : CrossingCoarseChunk037.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk037.checks] using CrossingCoarseChunk037.checks_true
  have h038 : CrossingCoarseChunk038.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk038.checks] using CrossingCoarseChunk038.checks_true
  have h039 : CrossingCoarseChunk039.pairs.all (crossingPairCheck) = true := by
    simpa only [CrossingCoarseChunk039.checks] using CrossingCoarseChunk039.checks_true
  simpa only [crossingCoarsePairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039,
    Bool.and_self]

def crossingCoarseInputs : List Interval :=
  ((List.range 1000).filter fun k =>
    k != 257 && k != 258 && k != 359 && k != 360) |>.map
    (uniformCell 0 1000000000)

set_option maxHeartbeats 0 in
theorem crossingCoarseMap_fst :
    crossingCoarsePairs.map Prod.fst = crossingCoarseInputs := by
  have h000 : CrossingCoarseChunk000.pairs.map Prod.fst = CrossingCoarseChunk000.inputs :=
    CrossingCoarseChunk000.map_fst
  have h001 : CrossingCoarseChunk001.pairs.map Prod.fst = CrossingCoarseChunk001.inputs :=
    CrossingCoarseChunk001.map_fst
  have h002 : CrossingCoarseChunk002.pairs.map Prod.fst = CrossingCoarseChunk002.inputs :=
    CrossingCoarseChunk002.map_fst
  have h003 : CrossingCoarseChunk003.pairs.map Prod.fst = CrossingCoarseChunk003.inputs :=
    CrossingCoarseChunk003.map_fst
  have h004 : CrossingCoarseChunk004.pairs.map Prod.fst = CrossingCoarseChunk004.inputs :=
    CrossingCoarseChunk004.map_fst
  have h005 : CrossingCoarseChunk005.pairs.map Prod.fst = CrossingCoarseChunk005.inputs :=
    CrossingCoarseChunk005.map_fst
  have h006 : CrossingCoarseChunk006.pairs.map Prod.fst = CrossingCoarseChunk006.inputs :=
    CrossingCoarseChunk006.map_fst
  have h007 : CrossingCoarseChunk007.pairs.map Prod.fst = CrossingCoarseChunk007.inputs :=
    CrossingCoarseChunk007.map_fst
  have h008 : CrossingCoarseChunk008.pairs.map Prod.fst = CrossingCoarseChunk008.inputs :=
    CrossingCoarseChunk008.map_fst
  have h009 : CrossingCoarseChunk009.pairs.map Prod.fst = CrossingCoarseChunk009.inputs :=
    CrossingCoarseChunk009.map_fst
  have h010 : CrossingCoarseChunk010.pairs.map Prod.fst = CrossingCoarseChunk010.inputs :=
    CrossingCoarseChunk010.map_fst
  have h011 : CrossingCoarseChunk011.pairs.map Prod.fst = CrossingCoarseChunk011.inputs :=
    CrossingCoarseChunk011.map_fst
  have h012 : CrossingCoarseChunk012.pairs.map Prod.fst = CrossingCoarseChunk012.inputs :=
    CrossingCoarseChunk012.map_fst
  have h013 : CrossingCoarseChunk013.pairs.map Prod.fst = CrossingCoarseChunk013.inputs :=
    CrossingCoarseChunk013.map_fst
  have h014 : CrossingCoarseChunk014.pairs.map Prod.fst = CrossingCoarseChunk014.inputs :=
    CrossingCoarseChunk014.map_fst
  have h015 : CrossingCoarseChunk015.pairs.map Prod.fst = CrossingCoarseChunk015.inputs :=
    CrossingCoarseChunk015.map_fst
  have h016 : CrossingCoarseChunk016.pairs.map Prod.fst = CrossingCoarseChunk016.inputs :=
    CrossingCoarseChunk016.map_fst
  have h017 : CrossingCoarseChunk017.pairs.map Prod.fst = CrossingCoarseChunk017.inputs :=
    CrossingCoarseChunk017.map_fst
  have h018 : CrossingCoarseChunk018.pairs.map Prod.fst = CrossingCoarseChunk018.inputs :=
    CrossingCoarseChunk018.map_fst
  have h019 : CrossingCoarseChunk019.pairs.map Prod.fst = CrossingCoarseChunk019.inputs :=
    CrossingCoarseChunk019.map_fst
  have h020 : CrossingCoarseChunk020.pairs.map Prod.fst = CrossingCoarseChunk020.inputs :=
    CrossingCoarseChunk020.map_fst
  have h021 : CrossingCoarseChunk021.pairs.map Prod.fst = CrossingCoarseChunk021.inputs :=
    CrossingCoarseChunk021.map_fst
  have h022 : CrossingCoarseChunk022.pairs.map Prod.fst = CrossingCoarseChunk022.inputs :=
    CrossingCoarseChunk022.map_fst
  have h023 : CrossingCoarseChunk023.pairs.map Prod.fst = CrossingCoarseChunk023.inputs :=
    CrossingCoarseChunk023.map_fst
  have h024 : CrossingCoarseChunk024.pairs.map Prod.fst = CrossingCoarseChunk024.inputs :=
    CrossingCoarseChunk024.map_fst
  have h025 : CrossingCoarseChunk025.pairs.map Prod.fst = CrossingCoarseChunk025.inputs :=
    CrossingCoarseChunk025.map_fst
  have h026 : CrossingCoarseChunk026.pairs.map Prod.fst = CrossingCoarseChunk026.inputs :=
    CrossingCoarseChunk026.map_fst
  have h027 : CrossingCoarseChunk027.pairs.map Prod.fst = CrossingCoarseChunk027.inputs :=
    CrossingCoarseChunk027.map_fst
  have h028 : CrossingCoarseChunk028.pairs.map Prod.fst = CrossingCoarseChunk028.inputs :=
    CrossingCoarseChunk028.map_fst
  have h029 : CrossingCoarseChunk029.pairs.map Prod.fst = CrossingCoarseChunk029.inputs :=
    CrossingCoarseChunk029.map_fst
  have h030 : CrossingCoarseChunk030.pairs.map Prod.fst = CrossingCoarseChunk030.inputs :=
    CrossingCoarseChunk030.map_fst
  have h031 : CrossingCoarseChunk031.pairs.map Prod.fst = CrossingCoarseChunk031.inputs :=
    CrossingCoarseChunk031.map_fst
  have h032 : CrossingCoarseChunk032.pairs.map Prod.fst = CrossingCoarseChunk032.inputs :=
    CrossingCoarseChunk032.map_fst
  have h033 : CrossingCoarseChunk033.pairs.map Prod.fst = CrossingCoarseChunk033.inputs :=
    CrossingCoarseChunk033.map_fst
  have h034 : CrossingCoarseChunk034.pairs.map Prod.fst = CrossingCoarseChunk034.inputs :=
    CrossingCoarseChunk034.map_fst
  have h035 : CrossingCoarseChunk035.pairs.map Prod.fst = CrossingCoarseChunk035.inputs :=
    CrossingCoarseChunk035.map_fst
  have h036 : CrossingCoarseChunk036.pairs.map Prod.fst = CrossingCoarseChunk036.inputs :=
    CrossingCoarseChunk036.map_fst
  have h037 : CrossingCoarseChunk037.pairs.map Prod.fst = CrossingCoarseChunk037.inputs :=
    CrossingCoarseChunk037.map_fst
  have h038 : CrossingCoarseChunk038.pairs.map Prod.fst = CrossingCoarseChunk038.inputs :=
    CrossingCoarseChunk038.map_fst
  have h039 : CrossingCoarseChunk039.pairs.map Prod.fst = CrossingCoarseChunk039.inputs :=
    CrossingCoarseChunk039.map_fst
  simp only [crossingCoarsePairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039]
  decide

theorem exists_checked_crossingCoarse (k : ℕ) (hk : k < 1000)
    (hk257 : k ≠ 257) (hk258 : k ≠ 258)
    (hk359 : k ≠ 359) (hk360 : k ≠ 360) :
    ∃ d : CrossingData, d.input = uniformCell 0 1000000000 k ∧
      crossingCheck d = true := by
  have hindex : k ∈ (List.range 1000).filter
      (fun j => j != 257 && j != 258 && j != 359 && j != 360) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr hk, by simp [hk257, hk258, hk359, hk360]⟩
  have hmem : uniformCell 0 1000000000 k ∈ crossingCoarseInputs :=
    List.mem_map.mpr ⟨k, hindex, rfl⟩
  rcases exists_of_map_fst crossingCoarseMap_fst crossingCoarseChecks_true hmem with
    ⟨d, hd⟩
  simp only [crossingPairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
