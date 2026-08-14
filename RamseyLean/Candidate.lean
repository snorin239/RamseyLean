import RamseyLean.Counting
import RamseyLean.Ramsey

/-!
# Candidates and goodness

The paper's basic inductive object is a pair `(X,Y)` of nonempty, disjoint
vertex sets.  A candidate is `(k,ℓ,t)`-good when `X ∪ Y` contains a red
`K_k`, `X` contains a blue `K_t`, or `Y` contains a blue `K_ℓ`.

Candidatehood and goodness are deliberately separate predicates.  In
particular, every construction of a smaller candidate must supply or derive
nonemptiness of both new sides.
-/

set_option autoImplicit false

namespace RamseyLean

open scoped Finset

universe u

variable {V : Type u}

/-- A paper candidate: two nonempty, disjoint vertex finsets in a red-blue
coloring.  The graph is an index so later statements retain their coloring. -/
structure Candidate (_G : SimpleGraph V) (X Y : Finset V) : Prop where
  left_nonempty : X.Nonempty
  right_nonempty : Y.Nonempty
  disjoint : Disjoint X Y

namespace Candidate

variable {G : SimpleGraph V}
variable {X Y X' Y' : Finset V}

/-- The left side of a candidate has positive cardinality. -/
theorem left_card_pos (h : Candidate G X Y) : 0 < #X :=
  h.left_nonempty.card_pos

/-- The right side of a candidate has positive cardinality. -/
theorem right_card_pos (h : Candidate G X Y) : 0 < #Y :=
  h.right_nonempty.card_pos

/-- Candidate sides may be exchanged. -/
theorem swap (h : Candidate G X Y) : Candidate G Y X :=
  ⟨h.right_nonempty, h.left_nonempty, h.disjoint.symm⟩

/-- The cardinality of the union of the two candidate sides. -/
theorem card_union [DecidableEq V] (h : Candidate G X Y) : #(X ∪ Y) = #X + #Y :=
  Finset.card_union_of_disjoint h.disjoint

/-- A vertex on the left of a candidate is not on its right. -/
theorem not_mem_right_of_mem_left (h : Candidate G X Y) {v : V} (hv : v ∈ X) :
    v ∉ Y :=
  Finset.disjoint_left.mp h.disjoint hv

/-- A vertex on the right of a candidate is not on its left. -/
theorem not_mem_left_of_mem_right (h : Candidate G X Y) {v : V} (hv : v ∈ Y) :
    v ∉ X :=
  Finset.disjoint_right.mp h.disjoint hv

/-- Nonempty subsets of the two sides form a subcandidate.  Nonemptiness is
explicit: arbitrary subsets are not silently promoted to candidates. -/
theorem subcandidate (h : Candidate G X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty) : Candidate G X' Y' :=
  ⟨hX', hY', h.disjoint.mono hX hY⟩

/-- Candidate-specialized density/count conversion. -/
theorem redDensity_mul_card [DecidableRel G.Adj] (h : Candidate G X Y) :
    redDensity G X Y * ((#X : ℝ) * (#Y : ℝ)) = redInteredgeCount G X Y :=
  RamseyLean.redDensity_mul_card h.left_nonempty h.right_nonempty

/-- Candidate-specialized excess/density conversion. -/
theorem excess_eq_density_sub_mul [DecidableRel G.Adj] (h : Candidate G X Y)
    (p : ℝ) :
    excess G p X Y = (redDensity G X Y - p) * ((#X : ℝ) * (#Y : ℝ)) :=
  RamseyLean.excess_eq_density_sub_mul h.left_nonempty h.right_nonempty

/-- Disjoint finsets with positive excess form a candidate.  This is the
interface used after selecting a positive-excess random bipartition. -/
theorem of_disjoint_of_excess_pos [DecidableRel G.Adj]
    (hdisjoint : Disjoint X Y) {p : ℝ} (hpos : 0 < excess G p X Y) :
    Candidate G X Y := by
  refine ⟨?_, ?_, hdisjoint⟩
  · by_contra hXnonempty
    rw [Finset.not_nonempty_iff_eq_empty] at hXnonempty
    subst X
    simp at hpos
  · by_contra hYnonempty
    rw [Finset.not_nonempty_iff_eq_empty] at hYnonempty
    subst Y
    simp at hpos

/-- Disjoint finsets with positive red density form a candidate. -/
theorem of_disjoint_of_redDensity_pos [DecidableRel G.Adj]
    (hdisjoint : Disjoint X Y) (hpos : 0 < redDensity G X Y) :
    Candidate G X Y := by
  refine ⟨?_, ?_, hdisjoint⟩
  · by_contra hXnonempty
    rw [Finset.not_nonempty_iff_eq_empty] at hXnonempty
    subst X
    simp at hpos
  · by_contra hYnonempty
    rw [Finset.not_nonempty_iff_eq_empty] at hYnonempty
    subst Y
    simp at hpos

/-- Positive excess derives the two nonemptiness obligations needed to turn
subsets of a candidate into a subcandidate. -/
theorem subcandidate_of_excess_pos [DecidableRel G.Adj]
    (h : Candidate G X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) {p : ℝ}
    (hpos : 0 < excess G p X' Y') : Candidate G X' Y' :=
  of_disjoint_of_excess_pos (h.disjoint.mono hX hY) hpos

/-- Positive red density likewise derives the nonemptiness obligations for a
subcandidate. -/
theorem subcandidate_of_redDensity_pos [DecidableRel G.Adj]
    (h : Candidate G X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hpos : 0 < redDensity G X' Y') : Candidate G X' Y' :=
  of_disjoint_of_redDensity_pos (h.disjoint.mono hX hY) hpos

variable [DecidableEq V]

/-- The paper's `(k,ℓ,t)`-goodness predicate.  The parameter order is the
printed order: the red target is `k`, the blue target on the right side `Y` is
`ℓ`, and the blue target on the left side `X` is `t`. -/
def IsGood (G : SimpleGraph V) (X Y : Finset V) (k ℓ t : ℕ) : Prop :=
  hasRedClique G (X ∪ Y) k ∨
    hasBlueClique G X t ∨ hasBlueClique G Y ℓ

namespace IsGood

variable {k ℓ t N : ℕ}

/-- A red clique in the union certifies goodness. -/
theorem of_red (h : hasRedClique G (X ∪ Y) k) : IsGood G X Y k ℓ t :=
  Or.inl h

/-- A blue clique on the left certifies goodness. -/
theorem of_blue_left (h : hasBlueClique G X t) : IsGood G X Y k ℓ t :=
  Or.inr (Or.inl h)

/-- A blue clique on the right certifies goodness. -/
theorem of_blue_right (h : hasBlueClique G Y ℓ) : IsGood G X Y k ℓ t :=
  Or.inr (Or.inr h)

/-- Goodness persists when both ambient sides are enlarged. -/
theorem mono (h : IsGood G X Y k ℓ t) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    IsGood G X' Y' k ℓ t := by
  rcases h with hred | hblueLeft | hblueRight
  · exact of_red (hasRedClique_mono (Finset.union_subset_union hX hY) hred)
  · exact of_blue_left (hasBlueClique_mono hX hblueLeft)
  · exact of_blue_right (hasBlueClique_mono hY hblueRight)

/-- Swapping candidate sides swaps the two blue clique parameters. -/
theorem swap (h : IsGood G X Y k ℓ t) : IsGood G Y X k t ℓ := by
  rcases h with hred | hblueLeft | hblueRight
  · exact of_red (by simpa [Finset.union_comm] using hred)
  · exact of_blue_right hblueLeft
  · exact of_blue_left hblueRight

/-- A Ramsey bound fitting inside the left side certifies goodness. -/
theorem of_ramseyBound_left (hbound : RamseyBound k t N) (hcard : N ≤ #X) :
    IsGood G X Y k ℓ t := by
  rcases (hbound.mono hcard).on_finset G X rfl with hred | hblue
  · exact of_red (hasRedClique_mono Finset.subset_union_left hred)
  · exact of_blue_left hblue

/-- A Ramsey bound fitting inside the right side certifies goodness. -/
theorem of_ramseyBound_right (hbound : RamseyBound k ℓ N) (hcard : N ≤ #Y) :
    IsGood G X Y k ℓ t := by
  rcases (hbound.mono hcard).on_finset G Y rfl with hred | hblue
  · exact of_red (hasRedClique_mono Finset.subset_union_right hred)
  · exact of_blue_right hblue

/-- The left-side cardinality form of `of_ramseyBound_left`. -/
theorem of_ramseyNumber_le_card_left (hcard : ramseyNumber k t ≤ #X) :
    IsGood G X Y k ℓ t :=
  of_ramseyBound_left (ramseyNumber_spec k t) hcard

/-- The right-side cardinality form used when the paper proves
`|Y| ≥ R(k,ℓ)`. -/
theorem of_ramseyNumber_le_card_right (hcard : ramseyNumber k ℓ ≤ #Y) :
    IsGood G X Y k ℓ t :=
  of_ramseyBound_right (ramseyNumber_spec k ℓ) hcard

/-- When the two blue targets agree, goodness yields the usual global Ramsey
alternative on the whole finite vertex type. -/
theorem to_univ [Fintype V] (h : IsGood G X Y k ℓ ℓ) :
    hasRedClique G Finset.univ k ∨ hasBlueClique G Finset.univ ℓ := by
  rcases h with hred | hblueLeft | hblueRight
  · exact Or.inl (hasRedClique_mono (Finset.subset_univ _) hred)
  · exact Or.inr (hasBlueClique_mono (Finset.subset_univ _) hblueLeft)
  · exact Or.inr (hasBlueClique_mono (Finset.subset_univ _) hblueRight)

section Extensions

variable [Fintype V]
variable {v : V}

/-- Lift goodness after a red-neighborhood induction step.  A red clique in
the smaller union is extended by `v`; either blue alternative is merely
transported to the original candidate sides. -/
theorem of_red_extension [DecidableRel G.Adj]
    (h : IsGood G X' Y' k ℓ t)
    (hneighbor : X' ∪ Y' ⊆ G.neighborFinset v)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hv : v ∈ X) :
    IsGood G X Y (k + 1) ℓ t := by
  rcases h with hred | hblueLeft | hblueRight
  · apply of_red
    apply hasRedClique_mono
      (Finset.insert_subset (Finset.mem_union_left Y hv) (Finset.union_subset_union hX hY))
    exact hasRedClique_insert_of_subset_neighborFinset hred hneighbor
  · exact of_blue_left (hasBlueClique_mono hX hblueLeft)
  · exact of_blue_right (hasBlueClique_mono hY hblueRight)

/-- Lift goodness after a blue-neighborhood induction step on the left side.
A blue clique in the smaller left side is extended by `v`. -/
theorem of_blue_extension_left [DecidableRel Gᶜ.Adj]
    (h : IsGood G X' Y' k ℓ t)
    (hneighbor : X' ⊆ Gᶜ.neighborFinset v)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hv : v ∈ X) :
    IsGood G X Y k ℓ (t + 1) := by
  rcases h with hred | hblueLeft | hblueRight
  · exact of_red (hasRedClique_mono (Finset.union_subset_union hX hY) hred)
  · apply of_blue_left
    apply hasBlueClique_mono (Finset.insert_subset hv hX)
    exact hasBlueClique_insert_of_subset_neighborFinset hblueLeft hneighbor
  · exact of_blue_right (hasBlueClique_mono hY hblueRight)

end Extensions

end IsGood

/-- Every candidate is good when the red target has size one. -/
theorem isGood_one_red (h : Candidate G X Y) (ℓ t : ℕ) : IsGood G X Y 1 ℓ t := by
  rcases h.left_nonempty with ⟨v, hv⟩
  apply IsGood.of_red
  refine ⟨{v}, ?_, ?_⟩
  · simp [hv]
  · simp [SimpleGraph.isNClique_iff]

/-- Every candidate is good when the left blue target has size one. -/
theorem isGood_one_blue_left (h : Candidate G X Y) (k ℓ : ℕ) :
    IsGood G X Y k ℓ 1 := by
  rcases h.left_nonempty with ⟨v, hv⟩
  apply IsGood.of_blue_left
  refine ⟨{v}, ?_, ?_⟩
  · simpa using hv
  · simp [SimpleGraph.isNClique_iff]

/-- Every candidate is good when the right blue target has size one. -/
theorem isGood_one_blue_right (h : Candidate G X Y) (k t : ℕ) :
    IsGood G X Y k 1 t := by
  rcases h.right_nonempty with ⟨v, hv⟩
  apply IsGood.of_blue_right
  refine ⟨{v}, ?_, ?_⟩
  · simpa using hv
  · simp [SimpleGraph.isNClique_iff]

end Candidate

end RamseyLean
