import RamseyLean.Analysis.IntervalExpression
import RamseyLean.Analysis.UniformMesh

/-!
# Mesh wrappers for interval expressions

These lemmas combine the exact floor meshes with the sound reflected interval
evaluator.  A continuum lower bound is reduced to one `Safe` check and one
rational lower-endpoint comparison for each mesh cell.
-/

set_option autoImplicit false

namespace RamseyLean.IntervalMesh

open Set
open IntervalExpression

noncomputable section

/-- Evaluator input interval for cell `k` of a unit mesh with `N` cells. -/
def unitInterval (N k : ℕ) : Interval :=
  Interval.ofBounds (UniformMesh.unitPoint N k) (UniformMesh.unitPoint N (k + 1))

/-- Evaluator input interval for cell `k` of the affine mesh on `[a,b]`. -/
def affineInterval (a b : ℝ) (N k : ℕ) : Interval :=
  Interval.ofBounds (UniformMesh.affinePoint a b N k)
    (UniformMesh.affinePoint a b N (k + 1))

/-- Reduce a lower bound on the closed unit interval to exact cell
certificates. -/
theorem eval_ge_of_unitMesh (N : ℕ) (hN : 0 < N) (e : Expr) (L : ℝ)
    (hcert : ∀ k : ℕ, k ≤ N →
      Expr.Safe (unitInterval N k) e ∧
        L ≤ (Expr.bound (unitInterval N k) e).lower)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    L ≤ Expr.eval r e := by
  let k := ⌊(N : ℝ) * r⌋₊
  have hmesh := UniformMesh.floor_mem_unitMesh N hN hr
  have hkN : k ≤ N := by simpa [k] using hmesh.1
  have hrange : r ∈ Icc (UniformMesh.unitPoint N k)
      (UniformMesh.unitPoint N (k + 1)) := by
    simpa [k] using hmesh.2
  have hrmem : (unitInterval N k).Contains r := Interval.contains_ofBounds hrange
  have hsound := Expr.bound_sound hrmem e (hcert k hkN).1
  exact (hcert k hkN).2.trans (Interval.contains_iff.mp hsound).1

/-- Reduce a lower bound on an arbitrary nondegenerate closed interval to
exact affine-cell certificates. -/
theorem eval_ge_of_affineMesh {a b : ℝ} (hab : a < b)
    (N : ℕ) (hN : 0 < N) (e : Expr) (L : ℝ)
    (hcert : ∀ k : ℕ, k ≤ N →
      Expr.Safe (affineInterval a b N k) e ∧
        L ≤ (Expr.bound (affineInterval a b N k) e).lower)
    {r : ℝ} (hr : r ∈ Icc a b) :
    L ≤ Expr.eval r e := by
  let u := (r - a) / (b - a)
  let k := ⌊(N : ℝ) * u⌋₊
  have hmesh := UniformMesh.floor_mem_affineMesh hab N hN hr
  have hkN : k ≤ N := by simpa [k, u] using hmesh.1
  have hrange : r ∈ Icc (UniformMesh.affinePoint a b N k)
      (UniformMesh.affinePoint a b N (k + 1)) := by
    simpa [k, u] using hmesh.2
  have hrmem : (affineInterval a b N k).Contains r :=
    Interval.contains_ofBounds hrange
  have hsound := Expr.bound_sound hrmem e (hcert k hkN).1
  exact (hcert k hkN).2.trans (Interval.contains_iff.mp hsound).1

end

end RamseyLean.IntervalMesh
