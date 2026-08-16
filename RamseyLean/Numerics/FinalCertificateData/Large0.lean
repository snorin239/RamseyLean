import RamseyLean.Numerics.FinalCertificateData.Large0Chunk000
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk001
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk002
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk003
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk004
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk005
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk006
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk007
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk008
import RamseyLean.Numerics.FinalCertificateData.Large0Chunk009

/-! Aggregated checked rows for the `Large0` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def large0Pairs : List (Interval × LargeData) :=
  Large0Chunk000.pairs ++
    Large0Chunk001.pairs ++
    Large0Chunk002.pairs ++
    Large0Chunk003.pairs ++
    Large0Chunk004.pairs ++
    Large0Chunk005.pairs ++
    Large0Chunk006.pairs ++
    Large0Chunk007.pairs ++
    Large0Chunk008.pairs ++
    Large0Chunk009.pairs

theorem large0Checks_true :
    large0Pairs.all (largePairCheck .cutNineTwentieths) = true := by
  have h000 : Large0Chunk000.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk000.checks] using Large0Chunk000.checks_true
  have h001 : Large0Chunk001.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk001.checks] using Large0Chunk001.checks_true
  have h002 : Large0Chunk002.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk002.checks] using Large0Chunk002.checks_true
  have h003 : Large0Chunk003.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk003.checks] using Large0Chunk003.checks_true
  have h004 : Large0Chunk004.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk004.checks] using Large0Chunk004.checks_true
  have h005 : Large0Chunk005.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk005.checks] using Large0Chunk005.checks_true
  have h006 : Large0Chunk006.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk006.checks] using Large0Chunk006.checks_true
  have h007 : Large0Chunk007.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk007.checks] using Large0Chunk007.checks_true
  have h008 : Large0Chunk008.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk008.checks] using Large0Chunk008.checks_true
  have h009 : Large0Chunk009.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large0Chunk009.checks] using Large0Chunk009.checks_true
  simpa only [large0Pairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009,
    Bool.and_self]

def large0Inputs : List Interval :=
  List.range 228 |>.map (uniformCell (361000000000) (50000000))

set_option maxHeartbeats 0 in
theorem large0Map_fst :
    large0Pairs.map Prod.fst = large0Inputs := by
  have h000 : Large0Chunk000.pairs.map Prod.fst = Large0Chunk000.inputs :=
    Large0Chunk000.map_fst
  have h001 : Large0Chunk001.pairs.map Prod.fst = Large0Chunk001.inputs :=
    Large0Chunk001.map_fst
  have h002 : Large0Chunk002.pairs.map Prod.fst = Large0Chunk002.inputs :=
    Large0Chunk002.map_fst
  have h003 : Large0Chunk003.pairs.map Prod.fst = Large0Chunk003.inputs :=
    Large0Chunk003.map_fst
  have h004 : Large0Chunk004.pairs.map Prod.fst = Large0Chunk004.inputs :=
    Large0Chunk004.map_fst
  have h005 : Large0Chunk005.pairs.map Prod.fst = Large0Chunk005.inputs :=
    Large0Chunk005.map_fst
  have h006 : Large0Chunk006.pairs.map Prod.fst = Large0Chunk006.inputs :=
    Large0Chunk006.map_fst
  have h007 : Large0Chunk007.pairs.map Prod.fst = Large0Chunk007.inputs :=
    Large0Chunk007.map_fst
  have h008 : Large0Chunk008.pairs.map Prod.fst = Large0Chunk008.inputs :=
    Large0Chunk008.map_fst
  have h009 : Large0Chunk009.pairs.map Prod.fst = Large0Chunk009.inputs :=
    Large0Chunk009.map_fst
  simp only [large0Pairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009]
  decide

theorem exists_checked_large0 (k : ℕ) (hk : k < 228) :
    ∃ d : LargeData, d.input = uniformCell (361000000000) (50000000) k ∧
      largeCheck .cutNineTwentieths d = true := by
  have hmemRange : k ∈ List.range 228 := List.mem_range.mpr hk
  have hmem : uniformCell (361000000000) (50000000) k ∈ large0Inputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst large0Map_fst large0Checks_true hmem with
    ⟨d, hd⟩
  simp only [largePairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
