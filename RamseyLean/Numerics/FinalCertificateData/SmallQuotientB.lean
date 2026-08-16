import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk000
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk001
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk002
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk003
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk004
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk005
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk006
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk007
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk008
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk009
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk010
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk011
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk012
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk013
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk014
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk015
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk016
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk017
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk018
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk019
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk020
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk021
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk022
import RamseyLean.Numerics.FinalCertificateData.SmallQuotientBChunk023

/-! Aggregated checked rows for the `SmallQuotientB` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def smallQuotientBPairs : List (Interval × SmallCoordinateQuotientData) :=
  SmallQuotientBChunk000.pairs ++
    SmallQuotientBChunk001.pairs ++
    SmallQuotientBChunk002.pairs ++
    SmallQuotientBChunk003.pairs ++
    SmallQuotientBChunk004.pairs ++
    SmallQuotientBChunk005.pairs ++
    SmallQuotientBChunk006.pairs ++
    SmallQuotientBChunk007.pairs ++
    SmallQuotientBChunk008.pairs ++
    SmallQuotientBChunk009.pairs ++
    SmallQuotientBChunk010.pairs ++
    SmallQuotientBChunk011.pairs ++
    SmallQuotientBChunk012.pairs ++
    SmallQuotientBChunk013.pairs ++
    SmallQuotientBChunk014.pairs ++
    SmallQuotientBChunk015.pairs ++
    SmallQuotientBChunk016.pairs ++
    SmallQuotientBChunk017.pairs ++
    SmallQuotientBChunk018.pairs ++
    SmallQuotientBChunk019.pairs ++
    SmallQuotientBChunk020.pairs ++
    SmallQuotientBChunk021.pairs ++
    SmallQuotientBChunk022.pairs ++
    SmallQuotientBChunk023.pairs

theorem smallQuotientBChecks_true :
    smallQuotientBPairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
  have h000 : SmallQuotientBChunk000.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk000.checks] using SmallQuotientBChunk000.checks_true
  have h001 : SmallQuotientBChunk001.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk001.checks] using SmallQuotientBChunk001.checks_true
  have h002 : SmallQuotientBChunk002.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk002.checks] using SmallQuotientBChunk002.checks_true
  have h003 : SmallQuotientBChunk003.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk003.checks] using SmallQuotientBChunk003.checks_true
  have h004 : SmallQuotientBChunk004.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk004.checks] using SmallQuotientBChunk004.checks_true
  have h005 : SmallQuotientBChunk005.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk005.checks] using SmallQuotientBChunk005.checks_true
  have h006 : SmallQuotientBChunk006.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk006.checks] using SmallQuotientBChunk006.checks_true
  have h007 : SmallQuotientBChunk007.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk007.checks] using SmallQuotientBChunk007.checks_true
  have h008 : SmallQuotientBChunk008.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk008.checks] using SmallQuotientBChunk008.checks_true
  have h009 : SmallQuotientBChunk009.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk009.checks] using SmallQuotientBChunk009.checks_true
  have h010 : SmallQuotientBChunk010.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk010.checks] using SmallQuotientBChunk010.checks_true
  have h011 : SmallQuotientBChunk011.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk011.checks] using SmallQuotientBChunk011.checks_true
  have h012 : SmallQuotientBChunk012.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk012.checks] using SmallQuotientBChunk012.checks_true
  have h013 : SmallQuotientBChunk013.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk013.checks] using SmallQuotientBChunk013.checks_true
  have h014 : SmallQuotientBChunk014.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk014.checks] using SmallQuotientBChunk014.checks_true
  have h015 : SmallQuotientBChunk015.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk015.checks] using SmallQuotientBChunk015.checks_true
  have h016 : SmallQuotientBChunk016.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk016.checks] using SmallQuotientBChunk016.checks_true
  have h017 : SmallQuotientBChunk017.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk017.checks] using SmallQuotientBChunk017.checks_true
  have h018 : SmallQuotientBChunk018.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk018.checks] using SmallQuotientBChunk018.checks_true
  have h019 : SmallQuotientBChunk019.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk019.checks] using SmallQuotientBChunk019.checks_true
  have h020 : SmallQuotientBChunk020.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk020.checks] using SmallQuotientBChunk020.checks_true
  have h021 : SmallQuotientBChunk021.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk021.checks] using SmallQuotientBChunk021.checks_true
  have h022 : SmallQuotientBChunk022.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk022.checks] using SmallQuotientBChunk022.checks_true
  have h023 : SmallQuotientBChunk023.pairs.all (smallCoordinateQuotientPairCheck .fifthCut) = true := by
    simpa only [SmallQuotientBChunk023.checks] using SmallQuotientBChunk023.checks_true
  simpa only [smallQuotientBPairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023,
    Bool.and_self]

def smallQuotientBInputs : List Interval :=
  List.range 580 |>.map (uniformCell (200000000000) (100000000))

set_option maxHeartbeats 0 in
theorem smallQuotientBMap_fst :
    smallQuotientBPairs.map Prod.fst = smallQuotientBInputs := by
  have h000 : SmallQuotientBChunk000.pairs.map Prod.fst = SmallQuotientBChunk000.inputs :=
    SmallQuotientBChunk000.map_fst
  have h001 : SmallQuotientBChunk001.pairs.map Prod.fst = SmallQuotientBChunk001.inputs :=
    SmallQuotientBChunk001.map_fst
  have h002 : SmallQuotientBChunk002.pairs.map Prod.fst = SmallQuotientBChunk002.inputs :=
    SmallQuotientBChunk002.map_fst
  have h003 : SmallQuotientBChunk003.pairs.map Prod.fst = SmallQuotientBChunk003.inputs :=
    SmallQuotientBChunk003.map_fst
  have h004 : SmallQuotientBChunk004.pairs.map Prod.fst = SmallQuotientBChunk004.inputs :=
    SmallQuotientBChunk004.map_fst
  have h005 : SmallQuotientBChunk005.pairs.map Prod.fst = SmallQuotientBChunk005.inputs :=
    SmallQuotientBChunk005.map_fst
  have h006 : SmallQuotientBChunk006.pairs.map Prod.fst = SmallQuotientBChunk006.inputs :=
    SmallQuotientBChunk006.map_fst
  have h007 : SmallQuotientBChunk007.pairs.map Prod.fst = SmallQuotientBChunk007.inputs :=
    SmallQuotientBChunk007.map_fst
  have h008 : SmallQuotientBChunk008.pairs.map Prod.fst = SmallQuotientBChunk008.inputs :=
    SmallQuotientBChunk008.map_fst
  have h009 : SmallQuotientBChunk009.pairs.map Prod.fst = SmallQuotientBChunk009.inputs :=
    SmallQuotientBChunk009.map_fst
  have h010 : SmallQuotientBChunk010.pairs.map Prod.fst = SmallQuotientBChunk010.inputs :=
    SmallQuotientBChunk010.map_fst
  have h011 : SmallQuotientBChunk011.pairs.map Prod.fst = SmallQuotientBChunk011.inputs :=
    SmallQuotientBChunk011.map_fst
  have h012 : SmallQuotientBChunk012.pairs.map Prod.fst = SmallQuotientBChunk012.inputs :=
    SmallQuotientBChunk012.map_fst
  have h013 : SmallQuotientBChunk013.pairs.map Prod.fst = SmallQuotientBChunk013.inputs :=
    SmallQuotientBChunk013.map_fst
  have h014 : SmallQuotientBChunk014.pairs.map Prod.fst = SmallQuotientBChunk014.inputs :=
    SmallQuotientBChunk014.map_fst
  have h015 : SmallQuotientBChunk015.pairs.map Prod.fst = SmallQuotientBChunk015.inputs :=
    SmallQuotientBChunk015.map_fst
  have h016 : SmallQuotientBChunk016.pairs.map Prod.fst = SmallQuotientBChunk016.inputs :=
    SmallQuotientBChunk016.map_fst
  have h017 : SmallQuotientBChunk017.pairs.map Prod.fst = SmallQuotientBChunk017.inputs :=
    SmallQuotientBChunk017.map_fst
  have h018 : SmallQuotientBChunk018.pairs.map Prod.fst = SmallQuotientBChunk018.inputs :=
    SmallQuotientBChunk018.map_fst
  have h019 : SmallQuotientBChunk019.pairs.map Prod.fst = SmallQuotientBChunk019.inputs :=
    SmallQuotientBChunk019.map_fst
  have h020 : SmallQuotientBChunk020.pairs.map Prod.fst = SmallQuotientBChunk020.inputs :=
    SmallQuotientBChunk020.map_fst
  have h021 : SmallQuotientBChunk021.pairs.map Prod.fst = SmallQuotientBChunk021.inputs :=
    SmallQuotientBChunk021.map_fst
  have h022 : SmallQuotientBChunk022.pairs.map Prod.fst = SmallQuotientBChunk022.inputs :=
    SmallQuotientBChunk022.map_fst
  have h023 : SmallQuotientBChunk023.pairs.map Prod.fst = SmallQuotientBChunk023.inputs :=
    SmallQuotientBChunk023.map_fst
  simp only [smallQuotientBPairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023]
  decide

theorem exists_checked_smallQuotientB (k : ℕ) (hk : k < 580) :
    ∃ d : SmallCoordinateQuotientData, d.small.input = uniformCell (200000000000) (100000000) k ∧
      d.small.band = .fifthCut ∧ smallCoordinateQuotientCheck d = true := by
  have hmemRange : k ∈ List.range 580 := List.mem_range.mpr hk
  have hmem : uniformCell (200000000000) (100000000) k ∈ smallQuotientBInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst smallQuotientBMap_fst smallQuotientBChecks_true hmem with
    ⟨d, hd⟩
  simp only [smallCoordinateQuotientPairCheck,
    intervalEq, recordEq, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact ⟨d, hd.1.1.symm, hd.1.2, hd.2⟩

end RamseyLean.FinalCertificate.Data
