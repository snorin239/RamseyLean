import RamseyLean.Coloring
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Real.Basic

/-!
# Counting red edges

This file supplies the real-valued counting interface used throughout the
paper. A red edge from `X` to `Y` is represented by an ordered pair in
`SimpleGraph.interedges`. When `X` and `Y` are disjoint, as they are for
paper candidates, this counts each crossing edge exactly once.
-/

set_option autoImplicit false

namespace RamseyLean

open scoped Finset

universe u

variable {V : Type u}

/-- The number of red edges with first endpoint in `X` and second endpoint in
`Y`. For disjoint finsets this is the paper's `e_R(X,Y)`. -/
def redInteredgeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℕ :=
  #(G.interedges X Y)

/-- The red edge density between two finsets, coerced from Mathlib's rational
`SimpleGraph.edgeDensity` to `ℝ`. It is zero if either finset is empty. -/
def redDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℝ :=
  G.edgeDensity X Y

/-- The excess number of red edges over density `p`:
`e_R(X,Y) - p |X| |Y|`. -/
def excess (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℝ) (X Y : Finset V) : ℝ :=
  redInteredgeCount G X Y - p * #X * #Y

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y Z : Finset V} {p : ℝ}

@[simp]
theorem redInteredgeCount_empty_left (Y : Finset V) :
    redInteredgeCount G ∅ Y = 0 := by
  simp [redInteredgeCount]

/-- Symmetry of the red interedge count. -/
theorem redInteredgeCount_comm (X Y : Finset V) :
    redInteredgeCount G X Y = redInteredgeCount G Y X := by
  change #(Rel.interedges G.Adj X Y) = #(Rel.interedges G.Adj Y X)
  have := G.symm
  exact Rel.card_interedges_comm X Y

@[simp]
theorem redInteredgeCount_empty_right (X : Finset V) :
    redInteredgeCount G X ∅ = 0 := by
  rw [redInteredgeCount_comm, redInteredgeCount_empty_left]

/-- The red interedge count is at most the number of ordered pairs. -/
theorem redInteredgeCount_le_mul (X Y : Finset V) :
    redInteredgeCount G X Y ≤ #X * #Y :=
  G.card_interedges_le_mul X Y

/-- Red interedge counts add when the left endpoint set is split into
disjoint pieces. -/
theorem redInteredgeCount_union_left [DecidableEq V]
    (hXY : Disjoint X Y) (Z : Finset V) :
    redInteredgeCount G (X ∪ Y) Z =
      redInteredgeCount G X Z + redInteredgeCount G Y Z := by
  unfold redInteredgeCount
  have hUnion : G.interedges (X ∪ Y) Z = G.interedges X Z ∪ G.interedges Y Z := by
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    tauto
  rw [hUnion, Finset.card_union_of_disjoint (G.interedges_disjoint_left hXY Z)]

/-- Red interedge counts add when the right endpoint set is split into
disjoint pieces. -/
theorem redInteredgeCount_union_right [DecidableEq V]
    (X : Finset V) (hYZ : Disjoint Y Z) :
    redInteredgeCount G X (Y ∪ Z) =
      redInteredgeCount G X Y + redInteredgeCount G X Z := by
  rw [redInteredgeCount_comm, redInteredgeCount_union_left hYZ,
    redInteredgeCount_comm Y, redInteredgeCount_comm Z]

section Finite

variable [Fintype V] [DecidableEq V]

/-- Red interedges are counted by summing restricted red-neighborhood sizes
over the left endpoint set. -/
theorem redInteredgeCount_eq_sum_card_neighborFinset_inter (X Y : Finset V) :
    redInteredgeCount G X Y = ∑ x ∈ X, #(G.neighborFinset x ∩ Y) := by
  classical
  change #(Rel.interedges G.Adj X Y) = _
  rw [Rel.interedges_eq_biUnion, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.card_map]
    congr 1
    ext y
    simp [and_comm]
  · intro x hx x' hx' hxx'
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_map] at hz hz'
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y', hy', hpair⟩ := hz'
    exact hxx' (Prod.mk.inj hpair).1.symm

/-- The symmetric restricted-neighborhood sum, over the right endpoint set. -/
theorem redInteredgeCount_eq_sum_card_neighborFinset_inter_right (X Y : Finset V) :
    redInteredgeCount G X Y = ∑ y ∈ Y, #(G.neighborFinset y ∩ X) := by
  change #(Rel.interedges G.Adj X Y) = _
  have := G.symm
  rw [Rel.card_interedges_comm X Y]
  exact redInteredgeCount_eq_sum_card_neighborFinset_inter (G := G) Y X

end Finite

/-- Real density expressed directly using the red interedge count. -/
theorem redDensity_eq_div (X Y : Finset V) :
    redDensity G X Y =
      (redInteredgeCount G X Y : ℝ) / ((#X : ℝ) * (#Y : ℝ)) := by
  simp [redDensity, SimpleGraph.edgeDensity_def, redInteredgeCount,
    Rat.cast_div, Rat.cast_natCast]

theorem redDensity_nonneg (X Y : Finset V) : 0 ≤ redDensity G X Y := by
  unfold redDensity
  exact_mod_cast G.edgeDensity_nonneg X Y

theorem redDensity_le_one (X Y : Finset V) : redDensity G X Y ≤ 1 := by
  unfold redDensity
  exact_mod_cast G.edgeDensity_le_one X Y

@[simp]
theorem redDensity_empty_left (Y : Finset V) : redDensity G ∅ Y = 0 := by
  simp [redDensity]

@[simp]
theorem redDensity_empty_right (X : Finset V) : redDensity G X ∅ = 0 := by
  simp [redDensity]

/-- Symmetry of real red density. -/
theorem redDensity_comm (X Y : Finset V) :
    redDensity G X Y = redDensity G Y X := by
  unfold redDensity
  rw [G.edgeDensity_comm]

/-- On nonempty endpoint sets, multiplying density by the number of ordered
pairs recovers the red interedge count. -/
theorem redDensity_mul_card (hX : X.Nonempty) (hY : Y.Nonempty) :
    redDensity G X Y * ((#X : ℝ) * (#Y : ℝ)) = redInteredgeCount G X Y := by
  rw [redDensity_eq_div, div_mul_cancel₀]
  exact mul_ne_zero (by exact_mod_cast hX.card_ne_zero) (by exact_mod_cast hY.card_ne_zero)

@[simp]
theorem excess_empty_left (p : ℝ) (Y : Finset V) : excess G p ∅ Y = 0 := by
  simp [excess]

@[simp]
theorem excess_empty_right (p : ℝ) (X : Finset V) : excess G p X ∅ = 0 := by
  simp [excess]

/-- Symmetry of excess. -/
theorem excess_comm (p : ℝ) (X Y : Finset V) :
    excess G p X Y = excess G p Y X := by
  unfold excess
  rw [redInteredgeCount_comm]
  ring

/-- On nonempty endpoint sets, excess is `(d(X,Y) - p) |X| |Y|`. -/
theorem excess_eq_density_sub_mul (hX : X.Nonempty) (hY : Y.Nonempty) :
    excess G p X Y =
      (redDensity G X Y - p) * ((#X : ℝ) * (#Y : ℝ)) := by
  unfold excess
  rw [← redDensity_mul_card hX hY]
  ring

/-- Excess is additive across a disjoint split of the left endpoint set. -/
theorem excess_union_left [DecidableEq V]
    (hXY : Disjoint X Y) (Z : Finset V) :
    excess G p (X ∪ Y) Z = excess G p X Z + excess G p Y Z := by
  unfold excess
  rw [redInteredgeCount_union_left hXY, Finset.card_union_of_disjoint hXY]
  push_cast
  ring

/-- Excess is additive across a disjoint split of the right endpoint set. -/
theorem excess_union_right [DecidableEq V]
    (X : Finset V) (hYZ : Disjoint Y Z) :
    excess G p X (Y ∪ Z) = excess G p X Y + excess G p X Z := by
  rw [excess_comm, excess_union_left hYZ, excess_comm p Y, excess_comm p Z]

end RamseyLean
