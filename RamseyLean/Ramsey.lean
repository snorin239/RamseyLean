import RamseyLean.Coloring
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Nat

/-!
# Two-color Ramsey numbers

The paper writes `R(k, ℓ)` for the least order of a complete graph whose every
red-blue edge-coloring contains a red `K_k` or a blue `K_ℓ`.  We first expose
the corresponding universal predicate `RamseyBound`, prove its finite-set
transport, order monotonicity, symmetry, and Erdős--Szekeres recurrence, and
only then define the least such order as `ramseyNumber`.

The definitions also cover zero clique parameters.  In that boundary case the
empty clique makes the least Ramsey number zero; the paper's statements use
positive parameters.
-/

set_option autoImplicit false

namespace RamseyLean

open scoped Finset

/-- `RamseyBound k ℓ N` means that every red-blue coloring of the complete
graph on `N` vertices has a red clique of size `k` or a blue clique of size
`ℓ`.  A coloring is represented by its red graph on `Fin N`. -/
def RamseyBound (k ℓ N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    hasRedClique G Finset.univ k ∨ hasBlueClique G Finset.univ ℓ

private theorem hasCliqueOn_of_comap
    {U V : Type*} [Fintype U] {G : SimpleGraph V} {X : Finset V} {n : ℕ}
    (f : U ↪ V) (hf : ∀ u, f u ∈ X)
    (h : hasCliqueOn (G.comap f) Finset.univ n) :
    hasCliqueOn G X n := by
  classical
  rcases h with ⟨S, -, hS⟩
  refine ⟨S.map f, ?_, (hS.map).mono (G.map_comap_le f)⟩
  intro v hv
  simp only [Finset.mem_map] at hv
  obtain ⟨u, -, rfl⟩ := hv
  exact hf u

/-- A Ramsey bound on `Fin N` applies to any `N`-element finset of vertices.
This is the restriction interface used by neighborhood arguments. -/
theorem RamseyBound.on_finset {k ℓ N : ℕ} (h : RamseyBound k ℓ N)
    {V : Type*} (G : SimpleGraph V) (X : Finset V) (hX : #X = N) :
    hasRedClique G X k ∨ hasBlueClique G X ℓ := by
  classical
  let e : Fin N ≃ X := (X.equivFinOfCardEq hX).symm
  let f : Fin N ↪ V :=
    { toFun := fun i ↦ (e i : V)
      inj' := fun i j hij ↦ e.injective (Subtype.ext hij) }
  have hf : ∀ i, f i ∈ X := fun i ↦ (e i).property
  rcases h (G.comap f) with hred | hblue
  · exact Or.inl (hasCliqueOn_of_comap f hf hred)
  · right
    apply hasCliqueOn_of_comap (G := Gᶜ) f hf
    have hcompl : (G.comap f)ᶜ = Gᶜ.comap f := by
      ext u v
      simp [f.injective.eq_iff]
    simpa only [hasBlueClique, hcompl] using hblue

/-- Ramsey bounds are monotone in the number of vertices. -/
theorem RamseyBound.mono {k ℓ N M : ℕ} (h : RamseyBound k ℓ N) (hNM : N ≤ M) :
    RamseyBound k ℓ M := by
  intro G
  classical
  obtain ⟨X, -, hX⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin M))) (by simpa using hNM)
  rcases h.on_finset G X hX with hred | hblue
  · exact Or.inl (hasRedClique_mono (Finset.subset_univ X) hred)
  · exact Or.inr (hasBlueClique_mono (Finset.subset_univ X) hblue)

/-- Swapping red and blue swaps the two clique parameters. -/
theorem RamseyBound.swap {k ℓ N : ℕ} (h : RamseyBound k ℓ N) :
    RamseyBound ℓ k N := by
  intro G
  rcases h Gᶜ with hblue | hred
  · exact Or.inr hblue
  · exact Or.inl (by simpa [hasBlueClique, hasRedClique] using hred)

theorem ramseyBound_comm {k ℓ N : ℕ} : RamseyBound k ℓ N ↔ RamseyBound ℓ k N :=
  ⟨RamseyBound.swap, RamseyBound.swap⟩

@[simp]
theorem ramseyBound_zero_left (ℓ N : ℕ) : RamseyBound 0 ℓ N := by
  intro G
  left
  exact ⟨∅, by simp, by simp⟩

@[simp]
theorem ramseyBound_zero_right (k N : ℕ) : RamseyBound k 0 N := by
  exact (ramseyBound_zero_left k N).swap

/-- One vertex always supplies a monochromatic clique of size one. -/
theorem ramseyBound_one_left (ℓ : ℕ) : RamseyBound 1 ℓ 1 := by
  intro G
  left
  refine ⟨Finset.univ, Finset.Subset.rfl, ?_⟩
  simp [SimpleGraph.isNClique_iff]

/-- The blue version of `ramseyBound_one_left`. -/
theorem ramseyBound_one_right (k : ℕ) : RamseyBound k 1 1 :=
  (ramseyBound_one_left k).swap

/-- A bound for two positive clique sizes must use a nonempty vertex set. -/
theorem RamseyBound.card_pos {k ℓ N : ℕ} (h : RamseyBound k ℓ N)
    (hk : 0 < k) (hℓ : 0 < ℓ) : 0 < N := by
  by_contra hN
  have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
  subst N
  rcases h (⊥ : SimpleGraph (Fin 0)) with hred | hblue
  · rcases hred with ⟨S, -, hS⟩
    have hSempty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun v _ ↦ Fin.elim0 v
    subst S
    have : k = 0 := by simpa using hS
    exact hk.ne' this
  · rcases hblue with ⟨S, -, hS⟩
    have hSempty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun v _ ↦ Fin.elim0 v
    subst S
    have : ℓ = 0 := by simpa using hS
    exact hℓ.ne' this

/-- The Erdős--Szekeres neighborhood recurrence in a successor form that
keeps both clique parameters positive:
`R(k+2,ℓ+2) ≤ R(k+1,ℓ+2) + R(k+2,ℓ+1)`. -/
theorem RamseyBound.recurrence {k ℓ N M : ℕ}
    (hred : RamseyBound (k + 1) (ℓ + 2) N)
    (hblue : RamseyBound (k + 2) (ℓ + 1) M) :
    RamseyBound (k + 2) (ℓ + 2) (N + M) := by
  intro G
  classical
  have hN : 0 < N := hred.card_pos (by omega) (by omega)
  have hNM : 0 < N + M := by omega
  let v : Fin (N + M) := ⟨0, hNM⟩
  by_cases hcard : N ≤ #(G.neighborFinset v)
  · obtain ⟨X, hXsub, hXcard⟩ :=
      Finset.exists_subset_card_eq (s := G.neighborFinset v) hcard
    rcases hred.on_finset G X hXcard with hK | hL
    · left
      apply hasRedClique_mono (Finset.subset_univ (insert v X))
      simpa [Nat.add_assoc] using
        hasRedClique_insert_of_subset_neighborFinset hK hXsub
    · exact Or.inr (hasBlueClique_mono (Finset.subset_univ X) hL)
  · have hredCard : #(G.neighborFinset v) < N := Nat.lt_of_not_ge hcard
    have hblueCard : #(Gᶜ.neighborFinset v) = N + M - 1 - #(G.neighborFinset v) := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using G.degree_compl v
    have hM : M ≤ #(Gᶜ.neighborFinset v) := by omega
    obtain ⟨Y, hYsub, hYcard⟩ :=
      Finset.exists_subset_card_eq (s := Gᶜ.neighborFinset v) hM
    rcases hblue.on_finset G Y hYcard with hK | hL
    · exact Or.inl (hasRedClique_mono (Finset.subset_univ Y) hK)
    · right
      apply hasBlueClique_mono (Finset.subset_univ (insert v Y))
      simpa [Nat.add_assoc] using
        hasBlueClique_insert_of_subset_neighborFinset hL hYsub

/-- Ramsey bounds exist for all natural clique parameters.  The proof follows
the Erdős--Szekeres recurrence; zero parameters use the empty clique and
one-vertex parameters use a singleton. -/
theorem exists_ramseyBound (k ℓ : ℕ) : ∃ N, RamseyBound k ℓ N := by
  induction k using Nat.twoStepInduction generalizing ℓ with
  | zero => exact ⟨0, ramseyBound_zero_left ℓ 0⟩
  | one => exact ⟨1, ramseyBound_one_left ℓ⟩
  | more k hk hk1 =>
      induction ℓ using Nat.twoStepInduction with
      | zero => exact ⟨0, ramseyBound_zero_right (k + 2) 0⟩
      | one => exact ⟨1, ramseyBound_one_right (k + 2)⟩
      | more ℓ hℓ hℓ1 =>
          obtain ⟨N, hN⟩ := hk1 (ℓ + 2)
          obtain ⟨M, hM⟩ := hℓ1
          exact ⟨N + M, hN.recurrence hM⟩

/-- The least order forcing a red `K_k` or a blue `K_ℓ`.  This is the paper's
two-color Ramsey number `R(k,ℓ)`.  For a zero parameter it is zero. -/
noncomputable def ramseyNumber (k ℓ : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_ramseyBound k ℓ)

/-- The least Ramsey number is itself a Ramsey bound. -/
theorem ramseyNumber_spec (k ℓ : ℕ) : RamseyBound k ℓ (ramseyNumber k ℓ) := by
  classical
  exact Nat.find_spec (exists_ramseyBound k ℓ)

/-- Minimality of `ramseyNumber`. -/
theorem ramseyNumber_le {k ℓ N : ℕ} (h : RamseyBound k ℓ N) :
    ramseyNumber k ℓ ≤ N := by
  classical
  exact Nat.find_min' (exists_ramseyBound k ℓ) h

/-- A natural number is a Ramsey bound exactly when it is at least the least
Ramsey number. -/
theorem ramseyBound_iff_ramseyNumber_le {k ℓ N : ℕ} :
    RamseyBound k ℓ N ↔ ramseyNumber k ℓ ≤ N := by
  constructor
  · exact ramseyNumber_le
  · intro h
    exact (ramseyNumber_spec k ℓ).mono h

theorem ramseyNumber_le_iff {k ℓ N : ℕ} :
    ramseyNumber k ℓ ≤ N ↔ RamseyBound k ℓ N :=
  ramseyBound_iff_ramseyNumber_le.symm

@[simp]
theorem ramseyNumber_zero_left (ℓ : ℕ) : ramseyNumber 0 ℓ = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact ramseyNumber_le (ramseyBound_zero_left ℓ 0)

@[simp]
theorem ramseyNumber_zero_right (k : ℕ) : ramseyNumber k 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact ramseyNumber_le (ramseyBound_zero_right k 0)

/-- Symmetry of the two-color Ramsey number. -/
theorem ramseyNumber_comm (k ℓ : ℕ) : ramseyNumber k ℓ = ramseyNumber ℓ k := by
  apply le_antisymm
  · exact ramseyNumber_le (ramseyNumber_spec ℓ k).swap
  · exact ramseyNumber_le (ramseyNumber_spec k ℓ).swap

/-- Positive clique parameters have a positive Ramsey number. -/
theorem ramseyNumber_pos {k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    0 < ramseyNumber k ℓ :=
  (ramseyNumber_spec k ℓ).card_pos hk hℓ

end RamseyLean
