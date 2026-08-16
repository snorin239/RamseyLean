import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk000
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk001
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk002
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk003
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk004
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk005
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk006
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk007
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk008
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk009
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk010
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk011
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk012
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk013
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk014
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk015
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk016
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk017
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk018
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk019
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk020
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk021
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk022
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk023
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk024
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk025
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk026
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk027
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk028
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk029
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk030
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk031
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk032
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk033
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk034
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk035
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk036
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk037
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk038
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientAChunk039

/-! Aggregated checked rows for the `SmallQuotientA` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def smallQuotientAPairs : List (Interval × SmallCoordinateQuotientData) :=
  SmallQuotientAChunk000.pairs ++
    SmallQuotientAChunk001.pairs ++
    SmallQuotientAChunk002.pairs ++
    SmallQuotientAChunk003.pairs ++
    SmallQuotientAChunk004.pairs ++
    SmallQuotientAChunk005.pairs ++
    SmallQuotientAChunk006.pairs ++
    SmallQuotientAChunk007.pairs ++
    SmallQuotientAChunk008.pairs ++
    SmallQuotientAChunk009.pairs ++
    SmallQuotientAChunk010.pairs ++
    SmallQuotientAChunk011.pairs ++
    SmallQuotientAChunk012.pairs ++
    SmallQuotientAChunk013.pairs ++
    SmallQuotientAChunk014.pairs ++
    SmallQuotientAChunk015.pairs ++
    SmallQuotientAChunk016.pairs ++
    SmallQuotientAChunk017.pairs ++
    SmallQuotientAChunk018.pairs ++
    SmallQuotientAChunk019.pairs ++
    SmallQuotientAChunk020.pairs ++
    SmallQuotientAChunk021.pairs ++
    SmallQuotientAChunk022.pairs ++
    SmallQuotientAChunk023.pairs ++
    SmallQuotientAChunk024.pairs ++
    SmallQuotientAChunk025.pairs ++
    SmallQuotientAChunk026.pairs ++
    SmallQuotientAChunk027.pairs ++
    SmallQuotientAChunk028.pairs ++
    SmallQuotientAChunk029.pairs ++
    SmallQuotientAChunk030.pairs ++
    SmallQuotientAChunk031.pairs ++
    SmallQuotientAChunk032.pairs ++
    SmallQuotientAChunk033.pairs ++
    SmallQuotientAChunk034.pairs ++
    SmallQuotientAChunk035.pairs ++
    SmallQuotientAChunk036.pairs ++
    SmallQuotientAChunk037.pairs ++
    SmallQuotientAChunk038.pairs ++
    SmallQuotientAChunk039.pairs

theorem smallQuotientAChecks_true :
    smallQuotientAPairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
  have h000 : SmallQuotientAChunk000.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk000.checks] using SmallQuotientAChunk000.checks_true
  have h001 : SmallQuotientAChunk001.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk001.checks] using SmallQuotientAChunk001.checks_true
  have h002 : SmallQuotientAChunk002.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk002.checks] using SmallQuotientAChunk002.checks_true
  have h003 : SmallQuotientAChunk003.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk003.checks] using SmallQuotientAChunk003.checks_true
  have h004 : SmallQuotientAChunk004.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk004.checks] using SmallQuotientAChunk004.checks_true
  have h005 : SmallQuotientAChunk005.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk005.checks] using SmallQuotientAChunk005.checks_true
  have h006 : SmallQuotientAChunk006.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk006.checks] using SmallQuotientAChunk006.checks_true
  have h007 : SmallQuotientAChunk007.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk007.checks] using SmallQuotientAChunk007.checks_true
  have h008 : SmallQuotientAChunk008.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk008.checks] using SmallQuotientAChunk008.checks_true
  have h009 : SmallQuotientAChunk009.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk009.checks] using SmallQuotientAChunk009.checks_true
  have h010 : SmallQuotientAChunk010.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk010.checks] using SmallQuotientAChunk010.checks_true
  have h011 : SmallQuotientAChunk011.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk011.checks] using SmallQuotientAChunk011.checks_true
  have h012 : SmallQuotientAChunk012.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk012.checks] using SmallQuotientAChunk012.checks_true
  have h013 : SmallQuotientAChunk013.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk013.checks] using SmallQuotientAChunk013.checks_true
  have h014 : SmallQuotientAChunk014.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk014.checks] using SmallQuotientAChunk014.checks_true
  have h015 : SmallQuotientAChunk015.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk015.checks] using SmallQuotientAChunk015.checks_true
  have h016 : SmallQuotientAChunk016.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk016.checks] using SmallQuotientAChunk016.checks_true
  have h017 : SmallQuotientAChunk017.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk017.checks] using SmallQuotientAChunk017.checks_true
  have h018 : SmallQuotientAChunk018.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk018.checks] using SmallQuotientAChunk018.checks_true
  have h019 : SmallQuotientAChunk019.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk019.checks] using SmallQuotientAChunk019.checks_true
  have h020 : SmallQuotientAChunk020.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk020.checks] using SmallQuotientAChunk020.checks_true
  have h021 : SmallQuotientAChunk021.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk021.checks] using SmallQuotientAChunk021.checks_true
  have h022 : SmallQuotientAChunk022.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk022.checks] using SmallQuotientAChunk022.checks_true
  have h023 : SmallQuotientAChunk023.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk023.checks] using SmallQuotientAChunk023.checks_true
  have h024 : SmallQuotientAChunk024.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk024.checks] using SmallQuotientAChunk024.checks_true
  have h025 : SmallQuotientAChunk025.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk025.checks] using SmallQuotientAChunk025.checks_true
  have h026 : SmallQuotientAChunk026.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk026.checks] using SmallQuotientAChunk026.checks_true
  have h027 : SmallQuotientAChunk027.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk027.checks] using SmallQuotientAChunk027.checks_true
  have h028 : SmallQuotientAChunk028.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk028.checks] using SmallQuotientAChunk028.checks_true
  have h029 : SmallQuotientAChunk029.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk029.checks] using SmallQuotientAChunk029.checks_true
  have h030 : SmallQuotientAChunk030.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk030.checks] using SmallQuotientAChunk030.checks_true
  have h031 : SmallQuotientAChunk031.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk031.checks] using SmallQuotientAChunk031.checks_true
  have h032 : SmallQuotientAChunk032.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk032.checks] using SmallQuotientAChunk032.checks_true
  have h033 : SmallQuotientAChunk033.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk033.checks] using SmallQuotientAChunk033.checks_true
  have h034 : SmallQuotientAChunk034.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk034.checks] using SmallQuotientAChunk034.checks_true
  have h035 : SmallQuotientAChunk035.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk035.checks] using SmallQuotientAChunk035.checks_true
  have h036 : SmallQuotientAChunk036.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk036.checks] using SmallQuotientAChunk036.checks_true
  have h037 : SmallQuotientAChunk037.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk037.checks] using SmallQuotientAChunk037.checks_true
  have h038 : SmallQuotientAChunk038.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk038.checks] using SmallQuotientAChunk038.checks_true
  have h039 : SmallQuotientAChunk039.pairs.all (smallCoordinateQuotientPairCheck .tenthFifth) = true := by
    simpa only [SmallQuotientAChunk039.checks] using SmallQuotientAChunk039.checks_true
  simpa only [smallQuotientAPairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039,
    Bool.and_self]

def smallQuotientAInputs : List Interval :=
  List.range 1000 |>.map (uniformCell (100000000000) (100000000))

set_option maxHeartbeats 0 in
theorem smallQuotientAMap_fst :
    smallQuotientAPairs.map Prod.fst = smallQuotientAInputs := by
  have h000 : SmallQuotientAChunk000.pairs.map Prod.fst = SmallQuotientAChunk000.inputs :=
    SmallQuotientAChunk000.map_fst
  have h001 : SmallQuotientAChunk001.pairs.map Prod.fst = SmallQuotientAChunk001.inputs :=
    SmallQuotientAChunk001.map_fst
  have h002 : SmallQuotientAChunk002.pairs.map Prod.fst = SmallQuotientAChunk002.inputs :=
    SmallQuotientAChunk002.map_fst
  have h003 : SmallQuotientAChunk003.pairs.map Prod.fst = SmallQuotientAChunk003.inputs :=
    SmallQuotientAChunk003.map_fst
  have h004 : SmallQuotientAChunk004.pairs.map Prod.fst = SmallQuotientAChunk004.inputs :=
    SmallQuotientAChunk004.map_fst
  have h005 : SmallQuotientAChunk005.pairs.map Prod.fst = SmallQuotientAChunk005.inputs :=
    SmallQuotientAChunk005.map_fst
  have h006 : SmallQuotientAChunk006.pairs.map Prod.fst = SmallQuotientAChunk006.inputs :=
    SmallQuotientAChunk006.map_fst
  have h007 : SmallQuotientAChunk007.pairs.map Prod.fst = SmallQuotientAChunk007.inputs :=
    SmallQuotientAChunk007.map_fst
  have h008 : SmallQuotientAChunk008.pairs.map Prod.fst = SmallQuotientAChunk008.inputs :=
    SmallQuotientAChunk008.map_fst
  have h009 : SmallQuotientAChunk009.pairs.map Prod.fst = SmallQuotientAChunk009.inputs :=
    SmallQuotientAChunk009.map_fst
  have h010 : SmallQuotientAChunk010.pairs.map Prod.fst = SmallQuotientAChunk010.inputs :=
    SmallQuotientAChunk010.map_fst
  have h011 : SmallQuotientAChunk011.pairs.map Prod.fst = SmallQuotientAChunk011.inputs :=
    SmallQuotientAChunk011.map_fst
  have h012 : SmallQuotientAChunk012.pairs.map Prod.fst = SmallQuotientAChunk012.inputs :=
    SmallQuotientAChunk012.map_fst
  have h013 : SmallQuotientAChunk013.pairs.map Prod.fst = SmallQuotientAChunk013.inputs :=
    SmallQuotientAChunk013.map_fst
  have h014 : SmallQuotientAChunk014.pairs.map Prod.fst = SmallQuotientAChunk014.inputs :=
    SmallQuotientAChunk014.map_fst
  have h015 : SmallQuotientAChunk015.pairs.map Prod.fst = SmallQuotientAChunk015.inputs :=
    SmallQuotientAChunk015.map_fst
  have h016 : SmallQuotientAChunk016.pairs.map Prod.fst = SmallQuotientAChunk016.inputs :=
    SmallQuotientAChunk016.map_fst
  have h017 : SmallQuotientAChunk017.pairs.map Prod.fst = SmallQuotientAChunk017.inputs :=
    SmallQuotientAChunk017.map_fst
  have h018 : SmallQuotientAChunk018.pairs.map Prod.fst = SmallQuotientAChunk018.inputs :=
    SmallQuotientAChunk018.map_fst
  have h019 : SmallQuotientAChunk019.pairs.map Prod.fst = SmallQuotientAChunk019.inputs :=
    SmallQuotientAChunk019.map_fst
  have h020 : SmallQuotientAChunk020.pairs.map Prod.fst = SmallQuotientAChunk020.inputs :=
    SmallQuotientAChunk020.map_fst
  have h021 : SmallQuotientAChunk021.pairs.map Prod.fst = SmallQuotientAChunk021.inputs :=
    SmallQuotientAChunk021.map_fst
  have h022 : SmallQuotientAChunk022.pairs.map Prod.fst = SmallQuotientAChunk022.inputs :=
    SmallQuotientAChunk022.map_fst
  have h023 : SmallQuotientAChunk023.pairs.map Prod.fst = SmallQuotientAChunk023.inputs :=
    SmallQuotientAChunk023.map_fst
  have h024 : SmallQuotientAChunk024.pairs.map Prod.fst = SmallQuotientAChunk024.inputs :=
    SmallQuotientAChunk024.map_fst
  have h025 : SmallQuotientAChunk025.pairs.map Prod.fst = SmallQuotientAChunk025.inputs :=
    SmallQuotientAChunk025.map_fst
  have h026 : SmallQuotientAChunk026.pairs.map Prod.fst = SmallQuotientAChunk026.inputs :=
    SmallQuotientAChunk026.map_fst
  have h027 : SmallQuotientAChunk027.pairs.map Prod.fst = SmallQuotientAChunk027.inputs :=
    SmallQuotientAChunk027.map_fst
  have h028 : SmallQuotientAChunk028.pairs.map Prod.fst = SmallQuotientAChunk028.inputs :=
    SmallQuotientAChunk028.map_fst
  have h029 : SmallQuotientAChunk029.pairs.map Prod.fst = SmallQuotientAChunk029.inputs :=
    SmallQuotientAChunk029.map_fst
  have h030 : SmallQuotientAChunk030.pairs.map Prod.fst = SmallQuotientAChunk030.inputs :=
    SmallQuotientAChunk030.map_fst
  have h031 : SmallQuotientAChunk031.pairs.map Prod.fst = SmallQuotientAChunk031.inputs :=
    SmallQuotientAChunk031.map_fst
  have h032 : SmallQuotientAChunk032.pairs.map Prod.fst = SmallQuotientAChunk032.inputs :=
    SmallQuotientAChunk032.map_fst
  have h033 : SmallQuotientAChunk033.pairs.map Prod.fst = SmallQuotientAChunk033.inputs :=
    SmallQuotientAChunk033.map_fst
  have h034 : SmallQuotientAChunk034.pairs.map Prod.fst = SmallQuotientAChunk034.inputs :=
    SmallQuotientAChunk034.map_fst
  have h035 : SmallQuotientAChunk035.pairs.map Prod.fst = SmallQuotientAChunk035.inputs :=
    SmallQuotientAChunk035.map_fst
  have h036 : SmallQuotientAChunk036.pairs.map Prod.fst = SmallQuotientAChunk036.inputs :=
    SmallQuotientAChunk036.map_fst
  have h037 : SmallQuotientAChunk037.pairs.map Prod.fst = SmallQuotientAChunk037.inputs :=
    SmallQuotientAChunk037.map_fst
  have h038 : SmallQuotientAChunk038.pairs.map Prod.fst = SmallQuotientAChunk038.inputs :=
    SmallQuotientAChunk038.map_fst
  have h039 : SmallQuotientAChunk039.pairs.map Prod.fst = SmallQuotientAChunk039.inputs :=
    SmallQuotientAChunk039.map_fst
  simp only [smallQuotientAPairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039]
  decide

theorem exists_checked_smallQuotientA (k : ℕ) (hk : k < 1000) :
    ∃ d : SmallCoordinateQuotientData, d.small.input = uniformCell (100000000000) (100000000) k ∧
      d.small.band = .tenthFifth ∧ smallCoordinateQuotientCheck d = true := by
  have hmemRange : k ∈ List.range 1000 := List.mem_range.mpr hk
  have hmem : uniformCell (100000000000) (100000000) k ∈ smallQuotientAInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst smallQuotientAMap_fst smallQuotientAChecks_true hmem with
    ⟨d, hd⟩
  simp only [smallCoordinateQuotientPairCheck,
    intervalEq, recordEq, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact ⟨d, hd.1.1.symm, hd.1.2, hd.2⟩

end RamseyLean.FinalCertificate.Data
