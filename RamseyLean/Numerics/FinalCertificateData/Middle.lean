import RamseyLean.Numerics.FinalCertificateData.MiddleChunk000
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk001
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk002
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk003
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk004
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk005
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk006
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk007
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk008
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk009
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk010
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk011
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk012
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk013
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk014
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk015
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk016
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk017
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk018
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk019
import RamseyLean.Numerics.FinalCertificateData.MiddleChunk020

/-! Aggregated checked rows for the `Middle` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def middlePairs : List (Interval × MiddleData) :=
  MiddleChunk000.pairs ++
    MiddleChunk001.pairs ++
    MiddleChunk002.pairs ++
    MiddleChunk003.pairs ++
    MiddleChunk004.pairs ++
    MiddleChunk005.pairs ++
    MiddleChunk006.pairs ++
    MiddleChunk007.pairs ++
    MiddleChunk008.pairs ++
    MiddleChunk009.pairs ++
    MiddleChunk010.pairs ++
    MiddleChunk011.pairs ++
    MiddleChunk012.pairs ++
    MiddleChunk013.pairs ++
    MiddleChunk014.pairs ++
    MiddleChunk015.pairs ++
    MiddleChunk016.pairs ++
    MiddleChunk017.pairs ++
    MiddleChunk018.pairs ++
    MiddleChunk019.pairs ++
    MiddleChunk020.pairs

theorem middleChecks_true :
    middlePairs.all (middlePairCheck) = true := by
  have h000 : MiddleChunk000.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk000.checks] using MiddleChunk000.checks_true
  have h001 : MiddleChunk001.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk001.checks] using MiddleChunk001.checks_true
  have h002 : MiddleChunk002.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk002.checks] using MiddleChunk002.checks_true
  have h003 : MiddleChunk003.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk003.checks] using MiddleChunk003.checks_true
  have h004 : MiddleChunk004.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk004.checks] using MiddleChunk004.checks_true
  have h005 : MiddleChunk005.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk005.checks] using MiddleChunk005.checks_true
  have h006 : MiddleChunk006.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk006.checks] using MiddleChunk006.checks_true
  have h007 : MiddleChunk007.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk007.checks] using MiddleChunk007.checks_true
  have h008 : MiddleChunk008.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk008.checks] using MiddleChunk008.checks_true
  have h009 : MiddleChunk009.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk009.checks] using MiddleChunk009.checks_true
  have h010 : MiddleChunk010.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk010.checks] using MiddleChunk010.checks_true
  have h011 : MiddleChunk011.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk011.checks] using MiddleChunk011.checks_true
  have h012 : MiddleChunk012.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk012.checks] using MiddleChunk012.checks_true
  have h013 : MiddleChunk013.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk013.checks] using MiddleChunk013.checks_true
  have h014 : MiddleChunk014.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk014.checks] using MiddleChunk014.checks_true
  have h015 : MiddleChunk015.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk015.checks] using MiddleChunk015.checks_true
  have h016 : MiddleChunk016.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk016.checks] using MiddleChunk016.checks_true
  have h017 : MiddleChunk017.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk017.checks] using MiddleChunk017.checks_true
  have h018 : MiddleChunk018.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk018.checks] using MiddleChunk018.checks_true
  have h019 : MiddleChunk019.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk019.checks] using MiddleChunk019.checks_true
  have h020 : MiddleChunk020.pairs.all (middlePairCheck) = true := by
    simpa only [MiddleChunk020.checks] using MiddleChunk020.checks_true
  simpa only [middlePairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020,
    Bool.and_self]

def middleInputs : List Interval :=
  List.range 514 |>.map (uniformCell (257800000000) (200000000))

set_option maxHeartbeats 0 in
theorem middleMap_fst :
    middlePairs.map Prod.fst = middleInputs := by
  have h000 : MiddleChunk000.pairs.map Prod.fst = MiddleChunk000.inputs :=
    MiddleChunk000.map_fst
  have h001 : MiddleChunk001.pairs.map Prod.fst = MiddleChunk001.inputs :=
    MiddleChunk001.map_fst
  have h002 : MiddleChunk002.pairs.map Prod.fst = MiddleChunk002.inputs :=
    MiddleChunk002.map_fst
  have h003 : MiddleChunk003.pairs.map Prod.fst = MiddleChunk003.inputs :=
    MiddleChunk003.map_fst
  have h004 : MiddleChunk004.pairs.map Prod.fst = MiddleChunk004.inputs :=
    MiddleChunk004.map_fst
  have h005 : MiddleChunk005.pairs.map Prod.fst = MiddleChunk005.inputs :=
    MiddleChunk005.map_fst
  have h006 : MiddleChunk006.pairs.map Prod.fst = MiddleChunk006.inputs :=
    MiddleChunk006.map_fst
  have h007 : MiddleChunk007.pairs.map Prod.fst = MiddleChunk007.inputs :=
    MiddleChunk007.map_fst
  have h008 : MiddleChunk008.pairs.map Prod.fst = MiddleChunk008.inputs :=
    MiddleChunk008.map_fst
  have h009 : MiddleChunk009.pairs.map Prod.fst = MiddleChunk009.inputs :=
    MiddleChunk009.map_fst
  have h010 : MiddleChunk010.pairs.map Prod.fst = MiddleChunk010.inputs :=
    MiddleChunk010.map_fst
  have h011 : MiddleChunk011.pairs.map Prod.fst = MiddleChunk011.inputs :=
    MiddleChunk011.map_fst
  have h012 : MiddleChunk012.pairs.map Prod.fst = MiddleChunk012.inputs :=
    MiddleChunk012.map_fst
  have h013 : MiddleChunk013.pairs.map Prod.fst = MiddleChunk013.inputs :=
    MiddleChunk013.map_fst
  have h014 : MiddleChunk014.pairs.map Prod.fst = MiddleChunk014.inputs :=
    MiddleChunk014.map_fst
  have h015 : MiddleChunk015.pairs.map Prod.fst = MiddleChunk015.inputs :=
    MiddleChunk015.map_fst
  have h016 : MiddleChunk016.pairs.map Prod.fst = MiddleChunk016.inputs :=
    MiddleChunk016.map_fst
  have h017 : MiddleChunk017.pairs.map Prod.fst = MiddleChunk017.inputs :=
    MiddleChunk017.map_fst
  have h018 : MiddleChunk018.pairs.map Prod.fst = MiddleChunk018.inputs :=
    MiddleChunk018.map_fst
  have h019 : MiddleChunk019.pairs.map Prod.fst = MiddleChunk019.inputs :=
    MiddleChunk019.map_fst
  have h020 : MiddleChunk020.pairs.map Prod.fst = MiddleChunk020.inputs :=
    MiddleChunk020.map_fst
  simp only [middlePairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020]
  decide

theorem exists_checked_middle (k : ℕ) (hk : k < 514) :
    ∃ d : MiddleData, d.input = uniformCell (257800000000) (200000000) k ∧
      middleCheck d = true := by
  have hmemRange : k ∈ List.range 514 := List.mem_range.mpr hk
  have hmem : uniformCell (257800000000) (200000000) k ∈ middleInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst middleMap_fst middleChecks_true hmem with
    ⟨d, hd⟩
  simp only [middlePairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
