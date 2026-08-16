import RamseyLean.Analysis.FixedPointInterval
import RamseyLean.Analysis.UniformMesh

/-!
# Exact fixed-point meshes for the final numerical certificate

All generated rows use integer endpoints on the fixed-point grid.  This module
connects the resulting uniform cells to the exact real affine mesh used to
select a cell containing an arbitrary point.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

/-- The `k`th closed cell of an integer fixed-point mesh. -/
def uniformCell (start step : ℤ) (k : ℕ) : Interval :=
  ⟨start + step * k, start + step * (k + 1)⟩

/-- Reindexing a suffix of a uniform mesh only changes its integer start. -/
theorem uniformCell_shift (base step : ℤ) (offset k : ℕ) :
    uniformCell (base + step * offset) step k =
      uniformCell base step (offset + k) := by
  unfold uniformCell
  congr 1 <;> push_cast <;> ring

private theorem value_mul_nat (z : ℤ) (k : ℕ) :
    value (z * k) = value z * k := by
  unfold value
  push_cast
  ring

/-- The fixed-point cell contains its corresponding exact affine mesh cell. -/
theorem uniformCell_contains {start step : ℤ} {N k : ℕ}
    (hN : 0 < N) (hstep : 0 < step) {r : ℝ}
    (hr : r ∈ Icc
      (UniformMesh.affinePoint (value start) (value (start + step * N)) N k)
      (UniformMesh.affinePoint (value start) (value (start + step * N)) N (k + 1))) :
    (uniformCell start step k).Contains r := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstepReal : 0 < value step := by
    unfold value
    exact div_pos (by exact_mod_cast hstep) scale_pos_real
  have hwidth : value (start + step * N) - value start = value step * N := by
    rw [value_add, value_mul_nat]
    ring
  constructor
  · calc
      value (uniformCell start step k).lo = value start + value step * k := by
        simp only [uniformCell, value_add, value_mul_nat]
      _ = UniformMesh.affinePoint (value start) (value (start + step * N)) N k := by
        rw [UniformMesh.affinePoint, UniformMesh.unitPoint, hwidth]
        field_simp [hNreal.ne']
      _ ≤ r := hr.1
  · calc
      r ≤ UniformMesh.affinePoint (value start) (value (start + step * N)) N (k + 1) :=
        hr.2
      _ = value (uniformCell start step k).hi := by
        rw [UniformMesh.affinePoint, UniformMesh.unitPoint, hwidth]
        simp only [uniformCell]
        rw [value_add]
        have hkcast : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by omega
        rw [hkcast, value_mul_nat]
        field_simp [hNreal.ne']

/-- An arbitrary point in a closed fixed-grid band lies in one of its `N`
certificate cells. -/
theorem exists_uniformCell {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step) {r : ℝ}
    (hr : r ∈ Icc (value start) (value (start + step * N))) :
    ∃ k : ℕ, k < N ∧ (uniformCell start step k).Contains r := by
  by_cases hend : r = value (start + step * N)
  · have hkLt : N - 1 < N := by omega
    refine ⟨N - 1, hkLt, ?_⟩
    rw [hend]
    constructor
    · change value (start + step * ((N - 1 : ℕ) : ℤ)) ≤
        value (start + step * (N : ℤ))
      unfold value
      have hk : ((N - 1 : ℕ) : ℤ) ≤ (N : ℤ) := by omega
      have hz : start + step * ((N - 1 : ℕ) : ℤ) ≤
          start + step * (N : ℤ) :=
        by simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hk hstep.le) start
      exact div_le_div_of_nonneg_right (by exact_mod_cast hz) scale_pos_real.le
    · change value (start + step * (N : ℤ)) ≤
        value (start + step * (((N - 1) + 1 : ℕ) : ℤ))
      rw [Nat.sub_add_cancel hN]
  · have hab : value start < value (start + step * N) := by
      rw [value_add, value_mul_nat]
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hstepReal : 0 < value step := by
        unfold value
        exact div_pos (by exact_mod_cast hstep) scale_pos_real
      nlinarith
    let u := (r - value start) / (value (start + step * N) - value start)
    let k := ⌊(N : ℝ) * u⌋₊
    have hmesh := UniformMesh.floor_mem_affineMesh hab N hN hr
    have hkLe : k ≤ N := by simpa [k, u] using hmesh.1
    have hkNe : k ≠ N := by
      intro hk
      have hrange :
          UniformMesh.affinePoint (value start) (value (start + step * N)) N k ≤ r := by
        simpa [k, u] using hmesh.2.1
      have hpoint :
          UniformMesh.affinePoint (value start) (value (start + step * N)) N N =
            value (start + step * N) := by
        rw [UniformMesh.affinePoint, UniformMesh.unitPoint]
        field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'] <;> ring
      rw [hk, hpoint] at hrange
      exact hend (le_antisymm hr.2 hrange)
    have hkLt : k < N := lt_of_le_of_ne hkLe hkNe
    refine ⟨k, hkLt, ?_⟩
    apply uniformCell_contains hN hstep
    simpa [k, u] using hmesh.2

end RamseyLean.FinalCertificate
