import RamseyLean.Numerics.FinalCertificateMesh
import RamseyLean.Numerics.FinalCertificateRowsBranches

/-! Shared row validators for generated final numerical certificates. -/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate.Data

open FixedPointInterval

/-- Compact notation used by generated fixed-point interval literals. -/
def iv (lo hi : ℤ) : Interval := ⟨lo, hi⟩

def smallCoordinatePairCheck (band : SmallBand)
    (p : Interval × SmallCoordinateData) : Bool :=
  intervalEq p.1 p.2.small.input && recordEq p.2.small.band band &&
    smallCoordinateCheck p.2

def smallCoordinateQuotientPairCheck (band : SmallBand)
    (p : Interval × SmallCoordinateQuotientData) : Bool :=
  intervalEq p.1 p.2.small.input && recordEq p.2.small.band band &&
    smallCoordinateQuotientCheck p.2

def middlePairCheck (p : Interval × MiddleData) : Bool :=
  intervalEq p.1 p.2.input && middleCheck p.2

def capPairCheck (p : Interval × LargeData) : Bool :=
  intervalEq p.1 p.2.input && capCheck p.2

def largePairCheck (band : LargeBand) (p : Interval × LargeData) : Bool :=
  intervalEq p.1 p.2.input && largeCheck band p.2

def crossingPairCheck (p : Interval × CrossingData) : Bool :=
  intervalEq p.1 p.2.input && crossingCheck p.2

/-- Extract the checked row paired with a listed mesh input. -/
theorem exists_of_map_fst {α : Type} {pairs : List (Interval × α)}
    {inputs : List Interval} {checker : Interval × α → Bool}
    (hMap : pairs.map Prod.fst = inputs)
    (hChecks : pairs.all checker = true) {I : Interval} (hI : I ∈ inputs) :
    ∃ d, checker (I, d) = true := by
  have hMapMem : I ∈ pairs.map Prod.fst := by
    rw [hMap]
    exact hI
  rcases List.mem_map.mp hMapMem with ⟨p, hp, hfst⟩
  rcases p with ⟨J, d⟩
  simp only at hfst
  subst J
  exact ⟨d, (List.all_eq_true.mp hChecks) (I, d) hp⟩

end RamseyLean.FinalCertificate.Data
