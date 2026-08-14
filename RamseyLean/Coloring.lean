import RamseyLean.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Red-blue colorings

The paper identifies a red-blue coloring of a complete graph with a simple
graph: adjacency is red, and adjacency in the complement is blue. This file
provides the finset-restricted clique predicates used by the Ramsey and
candidate layers, together with the basic restriction and neighborhood
lemmas needed by their inductions.
-/

set_option autoImplicit false

namespace RamseyLean

universe u

variable {V : Type u}

/-- `hasCliqueOn G X n` means that `X` contains a clique of exactly `n`
vertices in `G`. -/
def hasCliqueOn (G : SimpleGraph V) (X : Finset V) (n : ℕ) : Prop :=
  ∃ S : Finset V, S ⊆ X ∧ G.IsNClique n S

/-- `X` contains a red clique of exactly `n` vertices. Red edges are the
edges of `G`. -/
def hasRedClique (G : SimpleGraph V) (X : Finset V) (n : ℕ) : Prop :=
  hasCliqueOn G X n

/-- `X` contains a blue clique of exactly `n` vertices. Blue edges are the
edges of the complement `Gᶜ`. -/
def hasBlueClique (G : SimpleGraph V) (X : Finset V) (n : ℕ) : Prop :=
  hasCliqueOn Gᶜ X n

variable {G : SimpleGraph V} {X Y : Finset V} {n : ℕ}

/-- A clique contained in `X` is also contained in every larger finset. -/
theorem hasCliqueOn_mono (hXY : X ⊆ Y) : hasCliqueOn G X n → hasCliqueOn G Y n := by
  rintro ⟨S, hSX, hS⟩
  exact ⟨S, hSX.trans hXY, hS⟩

/-- Red-clique existence is monotone in the ambient finset. -/
theorem hasRedClique_mono (hXY : X ⊆ Y) :
    hasRedClique G X n → hasRedClique G Y n :=
  hasCliqueOn_mono hXY

/-- Blue-clique existence is monotone in the ambient finset. -/
theorem hasBlueClique_mono (hXY : X ⊆ Y) :
    hasBlueClique G X n → hasBlueClique G Y n :=
  hasCliqueOn_mono hXY

/-- The positive clique predicate is the negation of Mathlib's
`SimpleGraph.CliqueFreeOn` predicate. -/
theorem hasCliqueOn_iff_not_cliqueFreeOn :
    hasCliqueOn G X n ↔ ¬G.CliqueFreeOn (X : Set V) n := by
  classical
  constructor
  · rintro ⟨S, hSX, hS⟩ hfree
    exact hfree (Finset.coe_subset.mpr hSX) hS
  · intro hNotFree
    by_contra hNoClique
    apply hNotFree
    intro S hSX hS
    exact hNoClique ⟨S, Finset.coe_subset.mp hSX, hS⟩

/-- Red-clique existence on a finset is equivalent to failure of red
clique-freeness there. -/
theorem hasRedClique_iff_not_cliqueFreeOn :
    hasRedClique G X n ↔ ¬G.CliqueFreeOn (X : Set V) n :=
  hasCliqueOn_iff_not_cliqueFreeOn

/-- Blue-clique existence on a finset is equivalent to failure of blue
clique-freeness there. -/
theorem hasBlueClique_iff_not_cliqueFreeOn :
    hasBlueClique G X n ↔ ¬Gᶜ.CliqueFreeOn (X : Set V) n :=
  hasCliqueOn_iff_not_cliqueFreeOn

/-- On the full finite vertex set, red-clique existence is the negation of
`SimpleGraph.CliqueFree`. -/
theorem hasRedClique_univ_iff_not_cliqueFree [Fintype V] :
    hasRedClique G Finset.univ n ↔ ¬G.CliqueFree n := by
  rw [hasRedClique_iff_not_cliqueFreeOn]
  simp

/-- On the full finite vertex set, blue-clique existence is the negation of
clique-freeness in the complement. -/
theorem hasBlueClique_univ_iff_not_cliqueFree [Fintype V] :
    hasBlueClique G Finset.univ n ↔ ¬Gᶜ.CliqueFree n := by
  rw [hasBlueClique_iff_not_cliqueFreeOn]
  simp

variable {v : V}

/-- Adjoining a vertex adjacent to every vertex of an existing clique extends
that clique by one vertex. -/
theorem hasCliqueOn_insert_of_adj [DecidableEq V] (h : hasCliqueOn G X n)
    (hadj : ∀ w ∈ X, G.Adj v w) : hasCliqueOn G (insert v X) (n + 1) := by
  rcases h with ⟨S, hSX, hS⟩
  refine ⟨insert v S, Finset.insert_subset_insert v hSX, hS.insert ?_⟩
  intro w hw
  exact hadj w (hSX hw)

/-- A red clique inside the red neighborhood of `v` extends to a red clique
after adjoining `v`. -/
theorem hasRedClique_insert_of_subset_neighborFinset [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj]
    (h : hasRedClique G X n) (hX : X ⊆ G.neighborFinset v) :
    hasRedClique G (insert v X) (n + 1) := by
  apply hasCliqueOn_insert_of_adj h
  intro w hw
  exact (G.mem_neighborFinset v w).mp (hX hw)

/-- A blue clique inside the blue neighborhood of `v` extends to a blue
clique after adjoining `v`. -/
theorem hasBlueClique_insert_of_subset_neighborFinset [Fintype V] [DecidableEq V]
    [DecidableRel Gᶜ.Adj]
    (h : hasBlueClique G X n) (hX : X ⊆ Gᶜ.neighborFinset v) :
    hasBlueClique G (insert v X) (n + 1) := by
  apply hasCliqueOn_insert_of_adj h
  intro w hw
  exact (Gᶜ.mem_neighborFinset v w).mp (hX hw)

end RamseyLean
