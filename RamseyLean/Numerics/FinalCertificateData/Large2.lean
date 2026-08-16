import RamseyLean.Numerics.FinalCertificateData.Large2Chunk000
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk001
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk002
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk003
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk004
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk005
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk006
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk007
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk008
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk009
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk010
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk011
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk012
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk013
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk014
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk015
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk016
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk017
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk018
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk019
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk020
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk021
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk022
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk023
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk024
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk025
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk026
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk027
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk028
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk029
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk030
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk031
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk032
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk033
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk034
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk035
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk036
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk037
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk038
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk039
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk040
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk041
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk042
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk043
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk044
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk045
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk046
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk047
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk048
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk049
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk050
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk051
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk052
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk053
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk054
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk055
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk056
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk057
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk058
import RamseyLean.Numerics.FinalCertificateData.Large2Chunk059

/-! Aggregated checked rows for the `Large2` final-certificate mesh. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

noncomputable def large2Pairs : List (Interval × LargeData) :=
  Large2Chunk000.pairs ++
    Large2Chunk001.pairs ++
    Large2Chunk002.pairs ++
    Large2Chunk003.pairs ++
    Large2Chunk004.pairs ++
    Large2Chunk005.pairs ++
    Large2Chunk006.pairs ++
    Large2Chunk007.pairs ++
    Large2Chunk008.pairs ++
    Large2Chunk009.pairs ++
    Large2Chunk010.pairs ++
    Large2Chunk011.pairs ++
    Large2Chunk012.pairs ++
    Large2Chunk013.pairs ++
    Large2Chunk014.pairs ++
    Large2Chunk015.pairs ++
    Large2Chunk016.pairs ++
    Large2Chunk017.pairs ++
    Large2Chunk018.pairs ++
    Large2Chunk019.pairs ++
    Large2Chunk020.pairs ++
    Large2Chunk021.pairs ++
    Large2Chunk022.pairs ++
    Large2Chunk023.pairs ++
    Large2Chunk024.pairs ++
    Large2Chunk025.pairs ++
    Large2Chunk026.pairs ++
    Large2Chunk027.pairs ++
    Large2Chunk028.pairs ++
    Large2Chunk029.pairs ++
    Large2Chunk030.pairs ++
    Large2Chunk031.pairs ++
    Large2Chunk032.pairs ++
    Large2Chunk033.pairs ++
    Large2Chunk034.pairs ++
    Large2Chunk035.pairs ++
    Large2Chunk036.pairs ++
    Large2Chunk037.pairs ++
    Large2Chunk038.pairs ++
    Large2Chunk039.pairs ++
    Large2Chunk040.pairs ++
    Large2Chunk041.pairs ++
    Large2Chunk042.pairs ++
    Large2Chunk043.pairs ++
    Large2Chunk044.pairs ++
    Large2Chunk045.pairs ++
    Large2Chunk046.pairs ++
    Large2Chunk047.pairs ++
    Large2Chunk048.pairs ++
    Large2Chunk049.pairs ++
    Large2Chunk050.pairs ++
    Large2Chunk051.pairs ++
    Large2Chunk052.pairs ++
    Large2Chunk053.pairs ++
    Large2Chunk054.pairs ++
    Large2Chunk055.pairs ++
    Large2Chunk056.pairs ++
    Large2Chunk057.pairs ++
    Large2Chunk058.pairs ++
    Large2Chunk059.pairs

theorem large2Checks_true :
    large2Pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
  have h000 : Large2Chunk000.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk000.checks] using Large2Chunk000.checks_true
  have h001 : Large2Chunk001.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk001.checks] using Large2Chunk001.checks_true
  have h002 : Large2Chunk002.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk002.checks] using Large2Chunk002.checks_true
  have h003 : Large2Chunk003.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk003.checks] using Large2Chunk003.checks_true
  have h004 : Large2Chunk004.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk004.checks] using Large2Chunk004.checks_true
  have h005 : Large2Chunk005.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk005.checks] using Large2Chunk005.checks_true
  have h006 : Large2Chunk006.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk006.checks] using Large2Chunk006.checks_true
  have h007 : Large2Chunk007.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk007.checks] using Large2Chunk007.checks_true
  have h008 : Large2Chunk008.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk008.checks] using Large2Chunk008.checks_true
  have h009 : Large2Chunk009.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk009.checks] using Large2Chunk009.checks_true
  have h010 : Large2Chunk010.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk010.checks] using Large2Chunk010.checks_true
  have h011 : Large2Chunk011.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk011.checks] using Large2Chunk011.checks_true
  have h012 : Large2Chunk012.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk012.checks] using Large2Chunk012.checks_true
  have h013 : Large2Chunk013.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk013.checks] using Large2Chunk013.checks_true
  have h014 : Large2Chunk014.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk014.checks] using Large2Chunk014.checks_true
  have h015 : Large2Chunk015.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk015.checks] using Large2Chunk015.checks_true
  have h016 : Large2Chunk016.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk016.checks] using Large2Chunk016.checks_true
  have h017 : Large2Chunk017.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk017.checks] using Large2Chunk017.checks_true
  have h018 : Large2Chunk018.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk018.checks] using Large2Chunk018.checks_true
  have h019 : Large2Chunk019.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk019.checks] using Large2Chunk019.checks_true
  have h020 : Large2Chunk020.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk020.checks] using Large2Chunk020.checks_true
  have h021 : Large2Chunk021.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk021.checks] using Large2Chunk021.checks_true
  have h022 : Large2Chunk022.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk022.checks] using Large2Chunk022.checks_true
  have h023 : Large2Chunk023.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk023.checks] using Large2Chunk023.checks_true
  have h024 : Large2Chunk024.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk024.checks] using Large2Chunk024.checks_true
  have h025 : Large2Chunk025.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk025.checks] using Large2Chunk025.checks_true
  have h026 : Large2Chunk026.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk026.checks] using Large2Chunk026.checks_true
  have h027 : Large2Chunk027.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk027.checks] using Large2Chunk027.checks_true
  have h028 : Large2Chunk028.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk028.checks] using Large2Chunk028.checks_true
  have h029 : Large2Chunk029.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk029.checks] using Large2Chunk029.checks_true
  have h030 : Large2Chunk030.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk030.checks] using Large2Chunk030.checks_true
  have h031 : Large2Chunk031.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk031.checks] using Large2Chunk031.checks_true
  have h032 : Large2Chunk032.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk032.checks] using Large2Chunk032.checks_true
  have h033 : Large2Chunk033.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk033.checks] using Large2Chunk033.checks_true
  have h034 : Large2Chunk034.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk034.checks] using Large2Chunk034.checks_true
  have h035 : Large2Chunk035.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk035.checks] using Large2Chunk035.checks_true
  have h036 : Large2Chunk036.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk036.checks] using Large2Chunk036.checks_true
  have h037 : Large2Chunk037.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk037.checks] using Large2Chunk037.checks_true
  have h038 : Large2Chunk038.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk038.checks] using Large2Chunk038.checks_true
  have h039 : Large2Chunk039.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk039.checks] using Large2Chunk039.checks_true
  have h040 : Large2Chunk040.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk040.checks] using Large2Chunk040.checks_true
  have h041 : Large2Chunk041.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk041.checks] using Large2Chunk041.checks_true
  have h042 : Large2Chunk042.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk042.checks] using Large2Chunk042.checks_true
  have h043 : Large2Chunk043.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk043.checks] using Large2Chunk043.checks_true
  have h044 : Large2Chunk044.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk044.checks] using Large2Chunk044.checks_true
  have h045 : Large2Chunk045.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk045.checks] using Large2Chunk045.checks_true
  have h046 : Large2Chunk046.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk046.checks] using Large2Chunk046.checks_true
  have h047 : Large2Chunk047.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk047.checks] using Large2Chunk047.checks_true
  have h048 : Large2Chunk048.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk048.checks] using Large2Chunk048.checks_true
  have h049 : Large2Chunk049.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk049.checks] using Large2Chunk049.checks_true
  have h050 : Large2Chunk050.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk050.checks] using Large2Chunk050.checks_true
  have h051 : Large2Chunk051.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk051.checks] using Large2Chunk051.checks_true
  have h052 : Large2Chunk052.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk052.checks] using Large2Chunk052.checks_true
  have h053 : Large2Chunk053.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk053.checks] using Large2Chunk053.checks_true
  have h054 : Large2Chunk054.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk054.checks] using Large2Chunk054.checks_true
  have h055 : Large2Chunk055.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk055.checks] using Large2Chunk055.checks_true
  have h056 : Large2Chunk056.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk056.checks] using Large2Chunk056.checks_true
  have h057 : Large2Chunk057.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk057.checks] using Large2Chunk057.checks_true
  have h058 : Large2Chunk058.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk058.checks] using Large2Chunk058.checks_true
  have h059 : Large2Chunk059.pairs.all (largePairCheck .nineTwentiethsThreeFifths) = true := by
    simpa only [Large2Chunk059.checks] using Large2Chunk059.checks_true
  simpa only [large2Pairs, List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059,
    Bool.and_self]

def large2Inputs : List Interval :=
  List.range 1500 |>.map (uniformCell (450000000000) (100000000))

set_option maxHeartbeats 0 in
theorem large2Map_fst :
    large2Pairs.map Prod.fst = large2Inputs := by
  have h000 : Large2Chunk000.pairs.map Prod.fst = Large2Chunk000.inputs :=
    Large2Chunk000.map_fst
  have h001 : Large2Chunk001.pairs.map Prod.fst = Large2Chunk001.inputs :=
    Large2Chunk001.map_fst
  have h002 : Large2Chunk002.pairs.map Prod.fst = Large2Chunk002.inputs :=
    Large2Chunk002.map_fst
  have h003 : Large2Chunk003.pairs.map Prod.fst = Large2Chunk003.inputs :=
    Large2Chunk003.map_fst
  have h004 : Large2Chunk004.pairs.map Prod.fst = Large2Chunk004.inputs :=
    Large2Chunk004.map_fst
  have h005 : Large2Chunk005.pairs.map Prod.fst = Large2Chunk005.inputs :=
    Large2Chunk005.map_fst
  have h006 : Large2Chunk006.pairs.map Prod.fst = Large2Chunk006.inputs :=
    Large2Chunk006.map_fst
  have h007 : Large2Chunk007.pairs.map Prod.fst = Large2Chunk007.inputs :=
    Large2Chunk007.map_fst
  have h008 : Large2Chunk008.pairs.map Prod.fst = Large2Chunk008.inputs :=
    Large2Chunk008.map_fst
  have h009 : Large2Chunk009.pairs.map Prod.fst = Large2Chunk009.inputs :=
    Large2Chunk009.map_fst
  have h010 : Large2Chunk010.pairs.map Prod.fst = Large2Chunk010.inputs :=
    Large2Chunk010.map_fst
  have h011 : Large2Chunk011.pairs.map Prod.fst = Large2Chunk011.inputs :=
    Large2Chunk011.map_fst
  have h012 : Large2Chunk012.pairs.map Prod.fst = Large2Chunk012.inputs :=
    Large2Chunk012.map_fst
  have h013 : Large2Chunk013.pairs.map Prod.fst = Large2Chunk013.inputs :=
    Large2Chunk013.map_fst
  have h014 : Large2Chunk014.pairs.map Prod.fst = Large2Chunk014.inputs :=
    Large2Chunk014.map_fst
  have h015 : Large2Chunk015.pairs.map Prod.fst = Large2Chunk015.inputs :=
    Large2Chunk015.map_fst
  have h016 : Large2Chunk016.pairs.map Prod.fst = Large2Chunk016.inputs :=
    Large2Chunk016.map_fst
  have h017 : Large2Chunk017.pairs.map Prod.fst = Large2Chunk017.inputs :=
    Large2Chunk017.map_fst
  have h018 : Large2Chunk018.pairs.map Prod.fst = Large2Chunk018.inputs :=
    Large2Chunk018.map_fst
  have h019 : Large2Chunk019.pairs.map Prod.fst = Large2Chunk019.inputs :=
    Large2Chunk019.map_fst
  have h020 : Large2Chunk020.pairs.map Prod.fst = Large2Chunk020.inputs :=
    Large2Chunk020.map_fst
  have h021 : Large2Chunk021.pairs.map Prod.fst = Large2Chunk021.inputs :=
    Large2Chunk021.map_fst
  have h022 : Large2Chunk022.pairs.map Prod.fst = Large2Chunk022.inputs :=
    Large2Chunk022.map_fst
  have h023 : Large2Chunk023.pairs.map Prod.fst = Large2Chunk023.inputs :=
    Large2Chunk023.map_fst
  have h024 : Large2Chunk024.pairs.map Prod.fst = Large2Chunk024.inputs :=
    Large2Chunk024.map_fst
  have h025 : Large2Chunk025.pairs.map Prod.fst = Large2Chunk025.inputs :=
    Large2Chunk025.map_fst
  have h026 : Large2Chunk026.pairs.map Prod.fst = Large2Chunk026.inputs :=
    Large2Chunk026.map_fst
  have h027 : Large2Chunk027.pairs.map Prod.fst = Large2Chunk027.inputs :=
    Large2Chunk027.map_fst
  have h028 : Large2Chunk028.pairs.map Prod.fst = Large2Chunk028.inputs :=
    Large2Chunk028.map_fst
  have h029 : Large2Chunk029.pairs.map Prod.fst = Large2Chunk029.inputs :=
    Large2Chunk029.map_fst
  have h030 : Large2Chunk030.pairs.map Prod.fst = Large2Chunk030.inputs :=
    Large2Chunk030.map_fst
  have h031 : Large2Chunk031.pairs.map Prod.fst = Large2Chunk031.inputs :=
    Large2Chunk031.map_fst
  have h032 : Large2Chunk032.pairs.map Prod.fst = Large2Chunk032.inputs :=
    Large2Chunk032.map_fst
  have h033 : Large2Chunk033.pairs.map Prod.fst = Large2Chunk033.inputs :=
    Large2Chunk033.map_fst
  have h034 : Large2Chunk034.pairs.map Prod.fst = Large2Chunk034.inputs :=
    Large2Chunk034.map_fst
  have h035 : Large2Chunk035.pairs.map Prod.fst = Large2Chunk035.inputs :=
    Large2Chunk035.map_fst
  have h036 : Large2Chunk036.pairs.map Prod.fst = Large2Chunk036.inputs :=
    Large2Chunk036.map_fst
  have h037 : Large2Chunk037.pairs.map Prod.fst = Large2Chunk037.inputs :=
    Large2Chunk037.map_fst
  have h038 : Large2Chunk038.pairs.map Prod.fst = Large2Chunk038.inputs :=
    Large2Chunk038.map_fst
  have h039 : Large2Chunk039.pairs.map Prod.fst = Large2Chunk039.inputs :=
    Large2Chunk039.map_fst
  have h040 : Large2Chunk040.pairs.map Prod.fst = Large2Chunk040.inputs :=
    Large2Chunk040.map_fst
  have h041 : Large2Chunk041.pairs.map Prod.fst = Large2Chunk041.inputs :=
    Large2Chunk041.map_fst
  have h042 : Large2Chunk042.pairs.map Prod.fst = Large2Chunk042.inputs :=
    Large2Chunk042.map_fst
  have h043 : Large2Chunk043.pairs.map Prod.fst = Large2Chunk043.inputs :=
    Large2Chunk043.map_fst
  have h044 : Large2Chunk044.pairs.map Prod.fst = Large2Chunk044.inputs :=
    Large2Chunk044.map_fst
  have h045 : Large2Chunk045.pairs.map Prod.fst = Large2Chunk045.inputs :=
    Large2Chunk045.map_fst
  have h046 : Large2Chunk046.pairs.map Prod.fst = Large2Chunk046.inputs :=
    Large2Chunk046.map_fst
  have h047 : Large2Chunk047.pairs.map Prod.fst = Large2Chunk047.inputs :=
    Large2Chunk047.map_fst
  have h048 : Large2Chunk048.pairs.map Prod.fst = Large2Chunk048.inputs :=
    Large2Chunk048.map_fst
  have h049 : Large2Chunk049.pairs.map Prod.fst = Large2Chunk049.inputs :=
    Large2Chunk049.map_fst
  have h050 : Large2Chunk050.pairs.map Prod.fst = Large2Chunk050.inputs :=
    Large2Chunk050.map_fst
  have h051 : Large2Chunk051.pairs.map Prod.fst = Large2Chunk051.inputs :=
    Large2Chunk051.map_fst
  have h052 : Large2Chunk052.pairs.map Prod.fst = Large2Chunk052.inputs :=
    Large2Chunk052.map_fst
  have h053 : Large2Chunk053.pairs.map Prod.fst = Large2Chunk053.inputs :=
    Large2Chunk053.map_fst
  have h054 : Large2Chunk054.pairs.map Prod.fst = Large2Chunk054.inputs :=
    Large2Chunk054.map_fst
  have h055 : Large2Chunk055.pairs.map Prod.fst = Large2Chunk055.inputs :=
    Large2Chunk055.map_fst
  have h056 : Large2Chunk056.pairs.map Prod.fst = Large2Chunk056.inputs :=
    Large2Chunk056.map_fst
  have h057 : Large2Chunk057.pairs.map Prod.fst = Large2Chunk057.inputs :=
    Large2Chunk057.map_fst
  have h058 : Large2Chunk058.pairs.map Prod.fst = Large2Chunk058.inputs :=
    Large2Chunk058.map_fst
  have h059 : Large2Chunk059.pairs.map Prod.fst = Large2Chunk059.inputs :=
    Large2Chunk059.map_fst
  simp only [large2Pairs, List.map_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059]
  decide

theorem exists_checked_large2 (k : ℕ) (hk : k < 1500) :
    ∃ d : LargeData, d.input = uniformCell (450000000000) (100000000) k ∧
      largeCheck .nineTwentiethsThreeFifths d = true := by
  have hmemRange : k ∈ List.range 1500 := List.mem_range.mpr hk
  have hmem : uniformCell (450000000000) (100000000) k ∈ large2Inputs :=
    List.mem_map.mpr ⟨k, hmemRange, rfl⟩
  rcases exists_of_map_fst large2Map_fst large2Checks_true hmem with
    ⟨d, hd⟩
  simp only [largePairCheck, intervalEq, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  exact ⟨d, hd.1.symm, hd.2⟩

end RamseyLean.FinalCertificate.Data
