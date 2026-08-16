import RamseyLean.Analysis.FixedPointInterval
import RamseyLean.Analysis.UniformMesh

/-!
# Fixed-point mesh cells for the preliminary numerical certificate

This module connects exact affine meshes over the reals with the outward-rounded
integer intervals used by the fixed-point checker for the preliminary case of
paper Lemma `lem:numerics`.
-/

set_option autoImplicit false

namespace RamseyLean.PreliminaryCertificate

open Set
open FixedPointInterval

/-- Outward-rounded fixed-point cell corresponding to the `k`th affine mesh
cell between the exactly scaled endpoints `a` and `b`. -/
def affineCell (a b : ℤ) (N k : ℕ) : Interval :=
  let width := b - a
  ⟨a + downNat (width * k) N, a + upNat (width * (k + 1)) N⟩

private theorem value_affine_numerator (a b : ℤ) (k : ℕ) :
    value ((b - a) * (k : ℤ)) = (value b - value a) * (k : ℝ) := by
  unfold value
  push_cast
  field_simp [scale_pos_real.ne']

/-- The outward-rounded fixed-point cell contains the corresponding exact real
affine mesh cell. -/
theorem affineCell_contains {a b : ℤ} {N k : ℕ} (hN : 0 < N) {r : ℝ}
    (hr : r ∈ Icc (UniformMesh.affinePoint (value a) (value b) N k)
      (UniformMesh.affinePoint (value a) (value b) N (k + 1))) :
    (affineCell a b N k).Contains r := by
  constructor
  · calc
      value (a + downNat ((b - a) * k) N) =
          value a + value (downNat ((b - a) * k) N) := by
            rw [value_add]
      _ ≤ value a + value ((b - a) * k) / (N : ℝ) := by
        gcongr
        exact Interval.value_downNat_le _ hN
      _ = UniformMesh.affinePoint (value a) (value b) N k := by
        rw [value_affine_numerator]
        unfold UniformMesh.affinePoint UniformMesh.unitPoint
        ring
      _ ≤ r := hr.1
  · calc
      r ≤ UniformMesh.affinePoint (value a) (value b) N (k + 1) := hr.2
      _ = value a + value ((b - a) * (k + 1)) / (N : ℝ) := by
        unfold UniformMesh.affinePoint UniformMesh.unitPoint value
        push_cast
        field_simp [scale_pos_real.ne', (by positivity : (N : ℝ) ≠ 0)]
      _ ≤ value (a + upNat ((b - a) * (k + 1)) N) := by
        rw [value_add]
        gcongr
        exact Interval.value_le_upNat _ hN

end RamseyLean.PreliminaryCertificate
