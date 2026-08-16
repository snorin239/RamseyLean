import Mathlib.Tactic

/-!
# Exact rational meshes

This module turns a point of a real interval into the closed mesh cell selected
by a natural floor.  Numerical certificates use it to reduce a continuum
inequality to finitely many exact interval checks.
-/

set_option autoImplicit false

namespace RamseyLean.UniformMesh

open Set

/-- The point `k / N` in the uniform mesh of the unit interval. -/
noncomputable def unitPoint (N k : ℕ) : ℝ := (k : ℝ) / (N : ℝ)

/-- The natural floor selects a unit-interval cell containing `r`.  At `r = 1`
the selected index is `N`, and the harmless last cell extends to `1 + 1/N`. -/
theorem floor_mem_unitMesh (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    let k := ⌊(N : ℝ) * r⌋₊
    k ≤ N ∧ r ∈ Icc (unitPoint N k) (unitPoint N (k + 1)) := by
  let k := ⌊(N : ℝ) * r⌋₊
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNrnonneg : 0 ≤ (N : ℝ) * r := mul_nonneg hNreal.le hr.1
  have hkLower : (k : ℝ) ≤ (N : ℝ) * r := by
    simpa [k] using Nat.floor_le hNrnonneg
  have hkUpper : (N : ℝ) * r < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one ((N : ℝ) * r)
  have hkN : k ≤ N := by
    apply Nat.floor_le_of_le
    exact (mul_le_mul_of_nonneg_left hr.2 hNreal.le).trans_eq (mul_one (N : ℝ))
  refine ⟨hkN, ?_⟩
  constructor
  · unfold unitPoint
    apply (div_le_iff₀ hNreal).2
    change (k : ℝ) ≤ r * (N : ℝ)
    simpa [mul_comm] using hkLower
  · unfold unitPoint
    apply (le_div_iff₀ hNreal).2
    calc
      r * (N : ℝ) = (N : ℝ) * r := mul_comm _ _
      _ ≤ (k : ℝ) + 1 := hkUpper.le
      _ = (((k + 1 : ℕ) : ℝ)) := by norm_num

/-- The point obtained by affinely transporting `k / N` from `[0,1]` to
`[a,b]`. -/
noncomputable def affinePoint (a b : ℝ) (N k : ℕ) : ℝ :=
  a + (b - a) * unitPoint N k

/-- Affine version of `floor_mem_unitMesh`, used for adaptive subintervals. -/
theorem floor_mem_affineMesh {a b x : ℝ} (hab : a < b)
    (N : ℕ) (hN : 0 < N) (hx : x ∈ Icc a b) :
    let u := (x - a) / (b - a)
    let k := ⌊(N : ℝ) * u⌋₊
    k ≤ N ∧ x ∈ Icc (affinePoint a b N k) (affinePoint a b N (k + 1)) := by
  let u := (x - a) / (b - a)
  let k := ⌊(N : ℝ) * u⌋₊
  have hwidth : 0 < b - a := sub_pos.mpr hab
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hwidth.le
    · exact (div_le_one hwidth).2 (by linarith [hx.2])
  have hmesh := floor_mem_unitMesh N hN hu
  have hkN : k ≤ N := by simpa [k, u] using hmesh.1
  have hcell : u ∈ Icc (unitPoint N k) (unitPoint N (k + 1)) := by
    simpa [k, u] using hmesh.2
  have huEq : (b - a) * u = x - a := by
    dsimp [u]
    field_simp [hwidth.ne']
  refine ⟨hkN, ?_⟩
  constructor
  · have h := mul_le_mul_of_nonneg_left hcell.1 hwidth.le
    dsimp [affinePoint]
    linarith
  · have h := mul_le_mul_of_nonneg_left hcell.2 hwidth.le
    dsimp [affinePoint]
    linarith

end RamseyLean.UniformMesh


