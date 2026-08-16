import RamseyLean.Numerics.FinalCertificateData.Large1Chunk000
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk001
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk002
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk003
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk004
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk005
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk006
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk007
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk008
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk009
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk010
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk011
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk012
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk013
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk014
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk015
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk016
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk017
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk018
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk019
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk020
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk021
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk022
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk023
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk024
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk025
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk026
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk027
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk028
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk029
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk030
import RamseyLean.Numerics.FinalCertificateData.Large1Chunk031

/-! Aggregated checked rows for the `Large1` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def large1Pairs : List (Interval × LargeData) :=
  Large1Chunk000.pairs ++
    Large1Chunk001.pairs ++
    Large1Chunk002.pairs ++
    Large1Chunk003.pairs ++
    Large1Chunk004.pairs ++
    Large1Chunk005.pairs ++
    Large1Chunk006.pairs ++
    Large1Chunk007.pairs ++
    Large1Chunk008.pairs ++
    Large1Chunk009.pairs ++
    Large1Chunk010.pairs ++
    Large1Chunk011.pairs ++
    Large1Chunk012.pairs ++
    Large1Chunk013.pairs ++
    Large1Chunk014.pairs ++
    Large1Chunk015.pairs ++
    Large1Chunk016.pairs ++
    Large1Chunk017.pairs ++
    Large1Chunk018.pairs ++
    Large1Chunk019.pairs ++
    Large1Chunk020.pairs ++
    Large1Chunk021.pairs ++
    Large1Chunk022.pairs ++
    Large1Chunk023.pairs ++
    Large1Chunk024.pairs ++
    Large1Chunk025.pairs ++
    Large1Chunk026.pairs ++
    Large1Chunk027.pairs ++
    Large1Chunk028.pairs ++
    Large1Chunk029.pairs ++
    Large1Chunk030.pairs ++
    Large1Chunk031.pairs

theorem large1Checks_true :
    large1Pairs.all (largePairCheck .cutNineTwentieths) = true := by
  have h000 : Large1Chunk000.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk000.checks] using Large1Chunk000.checks_true
  have h001 : Large1Chunk001.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk001.checks] using Large1Chunk001.checks_true
  have h002 : Large1Chunk002.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk002.checks] using Large1Chunk002.checks_true
  have h003 : Large1Chunk003.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk003.checks] using Large1Chunk003.checks_true
  have h004 : Large1Chunk004.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk004.checks] using Large1Chunk004.checks_true
  have h005 : Large1Chunk005.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk005.checks] using Large1Chunk005.checks_true
  have h006 : Large1Chunk006.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk006.checks] using Large1Chunk006.checks_true
  have h007 : Large1Chunk007.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk007.checks] using Large1Chunk007.checks_true
  have h008 : Large1Chunk008.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk008.checks] using Large1Chunk008.checks_true
  have h009 : Large1Chunk009.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk009.checks] using Large1Chunk009.checks_true
  have h010 : Large1Chunk010.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk010.checks] using Large1Chunk010.checks_true
  have h011 : Large1Chunk011.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk011.checks] using Large1Chunk011.checks_true
  have h012 : Large1Chunk012.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk012.checks] using Large1Chunk012.checks_true
  have h013 : Large1Chunk013.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk013.checks] using Large1Chunk013.checks_true
  have h014 : Large1Chunk014.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk014.checks] using Large1Chunk014.checks_true
  have h015 : Large1Chunk015.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk015.checks] using Large1Chunk015.checks_true
  have h016 : Large1Chunk016.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk016.checks] using Large1Chunk016.checks_true
  have h017 : Large1Chunk017.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk017.checks] using Large1Chunk017.checks_true
  have h018 : Large1Chunk018.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk018.checks] using Large1Chunk018.checks_true
  have h019 : Large1Chunk019.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk019.checks] using Large1Chunk019.checks_true
  have h020 : Large1Chunk020.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk020.checks] using Large1Chunk020.checks_true
  have h021 : Large1Chunk021.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk021.checks] using Large1Chunk021.checks_true
  have h022 : Large1Chunk022.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk022.checks] using Large1Chunk022.checks_true
  have h023 : Large1Chunk023.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk023.checks] using Large1Chunk023.checks_true
  have h024 : Large1Chunk024.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk024.checks] using Large1Chunk024.checks_true
  have h025 : Large1Chunk025.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk025.checks] using Large1Chunk025.checks_true
  have h026 : Large1Chunk026.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk026.checks] using Large1Chunk026.checks_true
  have h027 : Large1Chunk027.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk027.checks] using Large1Chunk027.checks_true
  have h028 : Large1Chunk028.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk028.checks] using Large1Chunk028.checks_true
  have h029 : Large1Chunk029.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk029.checks] using Large1Chunk029.checks_true
  have h030 : Large1Chunk030.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk030.checks] using Large1Chunk030.checks_true
  have h031 : Large1Chunk031.pairs.all (largePairCheck .cutNineTwentieths) = true := by
    simpa only [Large1Chunk031.checks] using Large1Chunk031.checks_true
  simpa only [large1Pairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031,
    Bool.and_self]

def large1Inputs : List Interval :=
  List.range 776 |>.map (uniformCell (372400000000) (100000000))

set_option maxHeartbeats 0 in
theorem large1Map_fst :
    large1Pairs.map Prod.fst = large1Inputs := by
  have h000 : Large1Chunk000.pairs.map Prod.fst = Large1Chunk000.inputs :=
    Large1Chunk000.map_fst
  have h001 : Large1Chunk001.pairs.map Prod.fst = Large1Chunk001.inputs :=
    Large1Chunk001.map_fst
  have h002 : Large1Chunk002.pairs.map Prod.fst = Large1Chunk002.inputs :=
    Large1Chunk002.map_fst
  have h003 : Large1Chunk003.pairs.map Prod.fst = Large1Chunk003.inputs :=
    Large1Chunk003.map_fst
  have h004 : Large1Chunk004.pairs.map Prod.fst = Large1Chunk004.inputs :=
    Large1Chunk004.map_fst
  have h005 : Large1Chunk005.pairs.map Prod.fst = Large1Chunk005.inputs :=
    Large1Chunk005.map_fst
  have h006 : Large1Chunk006.pairs.map Prod.fst = Large1Chunk006.inputs :=
    Large1Chunk006.map_fst
  have h007 : Large1Chunk007.pairs.map Prod.fst = Large1Chunk007.inputs :=
    Large1Chunk007.map_fst
  have h008 : Large1Chunk008.pairs.map Prod.fst = Large1Chunk008.inputs :=
    Large1Chunk008.map_fst
  have h009 : Large1Chunk009.pairs.map Prod.fst = Large1Chunk009.inputs :=
    Large1Chunk009.map_fst
  have h010 : Large1Chunk010.pairs.map Prod.fst = Large1Chunk010.inputs :=
    Large1Chunk010.map_fst
  have h011 : Large1Chunk011.pairs.map Prod.fst = Large1Chunk011.inputs :=
    Large1Chunk011.map_fst
  have h012 : Large1Chunk012.pairs.map Prod.fst = Large1Chunk012.inputs :=
    Large1Chunk012.map_fst
  have h013 : Large1Chunk013.pairs.map Prod.fst = Large1Chunk013.inputs :=
    Large1Chunk013.map_fst
  have h014 : Large1Chunk014.pairs.map Prod.fst = Large1Chunk014.inputs :=
    Large1Chunk014.map_fst
  have h015 : Large1Chunk015.pairs.map Prod.fst = Large1Chunk015.inputs :=
    Large1Chunk015.map_fst
  have h016 : Large1Chunk016.pairs.map Prod.fst = Large1Chunk016.inputs :=
    Large1Chunk016.map_fst
  have h017 : Large1Chunk017.pairs.map Prod.fst = Large1Chunk017.inputs :=
    Large1Chunk017.map_fst
  have h018 : Large1Chunk018.pairs.map Prod.fst = Large1Chunk018.inputs :=
    Large1Chunk018.map_fst
  have h019 : Large1Chunk019.pairs.map Prod.fst = Large1Chunk019.inputs :=
    Large1Chunk019.map_fst
  have h020 : Large1Chunk020.pairs.map Prod.fst = Large1Chunk020.inputs :=
    Large1Chunk020.map_fst
  have h021 : Large1Chunk021.pairs.map Prod.fst = Large1Chunk021.inputs :=
    Large1Chunk021.map_fst
  have h022 : Large1Chunk022.pairs.map Prod.fst = Large1Chunk022.inputs :=
    Large1Chunk022.map_fst
  have h023 : Large1Chunk023.pairs.map Prod.fst = Large1Chunk023.inputs :=
    Large1Chunk023.map_fst
  have h024 : Large1Chunk024.pairs.map Prod.fst = Large1Chunk024.inputs :=
    Large1Chunk024.map_fst
  have h025 : Large1Chunk025.pairs.map Prod.fst = Large1Chunk025.inputs :=
    Large1Chunk025.map_fst
  have h026 : Large1Chunk026.pairs.map Prod.fst = Large1Chunk026.inputs :=
    Large1Chunk026.map_fst
  have h027 : Large1Chunk027.pairs.map Prod.fst = Large1Chunk027.inputs :=
    Large1Chunk027.map_fst
  have h028 : Large1Chunk028.pairs.map Prod.fst = Large1Chunk028.inputs :=
    Large1Chunk028.map_fst
  have h029 : Large1Chunk029.pairs.map Prod.fst = Large1Chunk029.inputs :=
    Large1Chunk029.map_fst
  have h030 : Large1Chunk030.pairs.map Prod.fst = Large1Chunk030.inputs :=
    Large1Chunk030.map_fst
  have h031 : Large1Chunk031.pairs.map Prod.fst = Large1Chunk031.inputs :=
    Large1Chunk031.map_fst
  simp only [large1Pairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031]
  decide

theorem exists_checked_large1 (k : ℕ) (hk : k < 776) :
    ∃ d : LargeData, d.input = uniformCell (372400000000) (100000000) k ∧
      largeCheck .cutNineTwentieths d = true := by
  have hmemRange : k ∈ List.range 776 := List.mem_range.mpr hk
  have hmem : uniformCell (372400000000) (100000000) k ∈ large1Inputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst large1Map_fst large1Checks_true hmem with
    ⟨d, hd⟩
  simp only [largePairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
