import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk000
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk001
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk002
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk003
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk004
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk005
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk006
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk007
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk008
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk009
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk010
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk011
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk012
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk013
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk014
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk015
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk016
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk017
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk018
import RamseyLean.Numerics.FinalCertificateData.SmallSeriesChunk019

/-! Aggregated checked rows for the `SmallSeries` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def smallSeriesPairs : List (Interval × SmallCoordinateData) :=
  SmallSeriesChunk000.pairs ++
    SmallSeriesChunk001.pairs ++
    SmallSeriesChunk002.pairs ++
    SmallSeriesChunk003.pairs ++
    SmallSeriesChunk004.pairs ++
    SmallSeriesChunk005.pairs ++
    SmallSeriesChunk006.pairs ++
    SmallSeriesChunk007.pairs ++
    SmallSeriesChunk008.pairs ++
    SmallSeriesChunk009.pairs ++
    SmallSeriesChunk010.pairs ++
    SmallSeriesChunk011.pairs ++
    SmallSeriesChunk012.pairs ++
    SmallSeriesChunk013.pairs ++
    SmallSeriesChunk014.pairs ++
    SmallSeriesChunk015.pairs ++
    SmallSeriesChunk016.pairs ++
    SmallSeriesChunk017.pairs ++
    SmallSeriesChunk018.pairs ++
    SmallSeriesChunk019.pairs

theorem smallSeriesChecks_true :
    smallSeriesPairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
  have h000 : SmallSeriesChunk000.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk000.checks] using SmallSeriesChunk000.checks_true
  have h001 : SmallSeriesChunk001.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk001.checks] using SmallSeriesChunk001.checks_true
  have h002 : SmallSeriesChunk002.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk002.checks] using SmallSeriesChunk002.checks_true
  have h003 : SmallSeriesChunk003.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk003.checks] using SmallSeriesChunk003.checks_true
  have h004 : SmallSeriesChunk004.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk004.checks] using SmallSeriesChunk004.checks_true
  have h005 : SmallSeriesChunk005.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk005.checks] using SmallSeriesChunk005.checks_true
  have h006 : SmallSeriesChunk006.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk006.checks] using SmallSeriesChunk006.checks_true
  have h007 : SmallSeriesChunk007.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk007.checks] using SmallSeriesChunk007.checks_true
  have h008 : SmallSeriesChunk008.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk008.checks] using SmallSeriesChunk008.checks_true
  have h009 : SmallSeriesChunk009.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk009.checks] using SmallSeriesChunk009.checks_true
  have h010 : SmallSeriesChunk010.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk010.checks] using SmallSeriesChunk010.checks_true
  have h011 : SmallSeriesChunk011.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk011.checks] using SmallSeriesChunk011.checks_true
  have h012 : SmallSeriesChunk012.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk012.checks] using SmallSeriesChunk012.checks_true
  have h013 : SmallSeriesChunk013.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk013.checks] using SmallSeriesChunk013.checks_true
  have h014 : SmallSeriesChunk014.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk014.checks] using SmallSeriesChunk014.checks_true
  have h015 : SmallSeriesChunk015.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk015.checks] using SmallSeriesChunk015.checks_true
  have h016 : SmallSeriesChunk016.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk016.checks] using SmallSeriesChunk016.checks_true
  have h017 : SmallSeriesChunk017.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk017.checks] using SmallSeriesChunk017.checks_true
  have h018 : SmallSeriesChunk018.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk018.checks] using SmallSeriesChunk018.checks_true
  have h019 : SmallSeriesChunk019.pairs.all (smallCoordinatePairCheck .zeroTenth) = true := by
    simpa only [SmallSeriesChunk019.checks] using SmallSeriesChunk019.checks_true
  simpa only [smallSeriesPairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019,
    Bool.and_self]

def smallSeriesInputs : List Interval :=
  List.range 500 |>.map (uniformCell (0) (200000000))

set_option maxHeartbeats 0 in
theorem smallSeriesMap_fst :
    smallSeriesPairs.map Prod.fst = smallSeriesInputs := by
  have h000 : SmallSeriesChunk000.pairs.map Prod.fst = SmallSeriesChunk000.inputs :=
    SmallSeriesChunk000.map_fst
  have h001 : SmallSeriesChunk001.pairs.map Prod.fst = SmallSeriesChunk001.inputs :=
    SmallSeriesChunk001.map_fst
  have h002 : SmallSeriesChunk002.pairs.map Prod.fst = SmallSeriesChunk002.inputs :=
    SmallSeriesChunk002.map_fst
  have h003 : SmallSeriesChunk003.pairs.map Prod.fst = SmallSeriesChunk003.inputs :=
    SmallSeriesChunk003.map_fst
  have h004 : SmallSeriesChunk004.pairs.map Prod.fst = SmallSeriesChunk004.inputs :=
    SmallSeriesChunk004.map_fst
  have h005 : SmallSeriesChunk005.pairs.map Prod.fst = SmallSeriesChunk005.inputs :=
    SmallSeriesChunk005.map_fst
  have h006 : SmallSeriesChunk006.pairs.map Prod.fst = SmallSeriesChunk006.inputs :=
    SmallSeriesChunk006.map_fst
  have h007 : SmallSeriesChunk007.pairs.map Prod.fst = SmallSeriesChunk007.inputs :=
    SmallSeriesChunk007.map_fst
  have h008 : SmallSeriesChunk008.pairs.map Prod.fst = SmallSeriesChunk008.inputs :=
    SmallSeriesChunk008.map_fst
  have h009 : SmallSeriesChunk009.pairs.map Prod.fst = SmallSeriesChunk009.inputs :=
    SmallSeriesChunk009.map_fst
  have h010 : SmallSeriesChunk010.pairs.map Prod.fst = SmallSeriesChunk010.inputs :=
    SmallSeriesChunk010.map_fst
  have h011 : SmallSeriesChunk011.pairs.map Prod.fst = SmallSeriesChunk011.inputs :=
    SmallSeriesChunk011.map_fst
  have h012 : SmallSeriesChunk012.pairs.map Prod.fst = SmallSeriesChunk012.inputs :=
    SmallSeriesChunk012.map_fst
  have h013 : SmallSeriesChunk013.pairs.map Prod.fst = SmallSeriesChunk013.inputs :=
    SmallSeriesChunk013.map_fst
  have h014 : SmallSeriesChunk014.pairs.map Prod.fst = SmallSeriesChunk014.inputs :=
    SmallSeriesChunk014.map_fst
  have h015 : SmallSeriesChunk015.pairs.map Prod.fst = SmallSeriesChunk015.inputs :=
    SmallSeriesChunk015.map_fst
  have h016 : SmallSeriesChunk016.pairs.map Prod.fst = SmallSeriesChunk016.inputs :=
    SmallSeriesChunk016.map_fst
  have h017 : SmallSeriesChunk017.pairs.map Prod.fst = SmallSeriesChunk017.inputs :=
    SmallSeriesChunk017.map_fst
  have h018 : SmallSeriesChunk018.pairs.map Prod.fst = SmallSeriesChunk018.inputs :=
    SmallSeriesChunk018.map_fst
  have h019 : SmallSeriesChunk019.pairs.map Prod.fst = SmallSeriesChunk019.inputs :=
    SmallSeriesChunk019.map_fst
  simp only [smallSeriesPairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019]
  decide

theorem exists_checked_smallSeries (k : ℕ) (hk : k < 500) :
    ∃ d : SmallCoordinateData, d.small.input = uniformCell (0) (200000000) k ∧
      d.small.band = .zeroTenth ∧ smallCoordinateCheck d = true := by
  have hmemRange : k ∈ List.range 500 := List.mem_range.mpr hk
  have hmem : uniformCell (0) (200000000) k ∈ smallSeriesInputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst smallSeriesMap_fst smallSeriesChecks_true hmem with
    ⟨d, hd⟩
  simp only [smallCoordinatePairCheck,
    intervalEq, recordEq, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact ⟨d, hd.1.1.symm, hd.1.2, hd.2⟩

end RamseyLean.FinalCertificate.Data
