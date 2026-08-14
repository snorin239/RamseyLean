import RamseyLean.Candidate
import RamseyLean.Analysis.Binomial
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# Blue books

A blue book has a blue-clique spine and blue edges from every spine vertex to
every page vertex. This module supplies clique-extension interfaces and the
finite averaging argument of paper Lemma `l:BBook`.
-/

set_option autoImplicit false

namespace RamseyLean

open scoped Finset

universe u

variable {V : Type u}

/-- A blue book consists of a blue-clique spine `S` whose vertices are blue
adjacent to every vertex on the pages `T`. The cross-edge condition itself
forces the two finsets to be disjoint. -/
structure BlueBook (G : SimpleGraph V) (S T : Finset V) : Prop where
  spine_blue : Gᶜ.IsClique (S : Set V)
  cross_blue : Gᶜ.IsCompleteBetween (S : Set V) (T : Set V)

namespace BlueBook

variable {G : SimpleGraph V} {S T : Finset V}

/-- The spine and pages of a blue book are disjoint. -/
theorem disjoint [DecidableEq V] (h : BlueBook G S T) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro v hvS hvT
  exact Gᶜ.irrefl (h.cross_blue hvS hvT)

/-- Any requested number of spine vertices forms a blue clique. -/
theorem hasBlueClique_spine_of_le [DecidableEq V] (h : BlueBook G S T)
    {b : ℕ} (hb : b ≤ #S) : hasBlueClique G S b := by
  obtain ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq hb
  exact ⟨S', hS'S,
    ⟨h.spine_blue.subset (Finset.coe_subset.mpr hS'S), hS'card⟩⟩

/-- A blue clique in the pages of a blue book extends across its spine. -/
theorem extend_blueClique [DecidableEq V] (h : BlueBook G S T) {a : ℕ}
    (hT : hasBlueClique G T a) :
    hasBlueClique G (S ∪ T) (#S + a) := by
  rcases hT with ⟨A, hAT, hA⟩
  have hSA : Disjoint S A := h.disjoint.mono Finset.Subset.rfl hAT
  refine ⟨S ∪ A, Finset.union_subset_union Finset.Subset.rfl hAT, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isClique_iff, Finset.coe_union, Set.pairwise_union]
    refine ⟨h.spine_blue, hA.isClique, ?_⟩
    intro s hs a ha hne
    exact ⟨h.cross_blue hs (hAT ha), (h.cross_blue hs (hAT ha)).symm⟩
  · rw [Finset.card_union_of_disjoint hSA, hA.card_eq]

end BlueBook

namespace Candidate.IsGood

variable {G : SimpleGraph V} {S T X Y : Finset V}

/-- A good page candidate lifts through a blue-book spine. -/
theorem of_blueBook_extension [DecidableEq V]
    {k l t b : ℕ} (hbook : BlueBook G S T)
    (hgood : Candidate.IsGood G T Y k l (t - b))
    (hST : S ∪ T ⊆ X) (hS : #S = b) (hbt : b ≤ t) :
    Candidate.IsGood G X Y k l t := by
  have hTsub : T ⊆ X := Finset.subset_union_right.trans hST
  rcases hgood with hred | hblue | hright
  · exact of_red (hasRedClique_mono
      (Finset.union_subset_union hTsub Finset.Subset.rfl) hred)
  · apply of_blue_left
    apply hasBlueClique_mono hST
    have hext := hbook.extend_blueClique hblue
    convert hext using 1
    omega
  · exact of_blue_right hright

end Candidate.IsGood

section Finite

variable [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Page vertices in `Q` that are blue-adjacent to every vertex of `S`. -/
def commonBlueNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Q : Finset V) : Finset V :=
  Q.filter fun v => S ⊆ Gᶜ.neighborFinset v

/-- Vertices of `X` with at least `μ |X|` blue neighbors inside `X`. -/
noncomputable def highBlueVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (μ : ℝ) : Finset V :=
  X.filter fun v =>
    μ * (#X : ℝ) ≤ (#(Gᶜ.neighborFinset v ∩ X) : ℝ)

omit [Fintype V] in
private theorem card_powersetCard_below (U B : Finset V) (b : ℕ) :
    #((U.powersetCard b).filter fun S => S ⊆ B) = (#(B ∩ U)).choose b := by
  have hfilter :
      (U.powersetCard b).filter (fun S => S ⊆ B) =
        (B ∩ U).powersetCard b := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_inter_iff]
    tauto
  rw [hfilter, Finset.card_powersetCard]

private theorem sum_card_commonBlueNeighbors (U Q : Finset V) (b : ℕ) :
    (∑ S ∈ U.powersetCard b, #(commonBlueNeighbors G S Q)) =
      ∑ v ∈ Q, (#(Gᶜ.neighborFinset v ∩ U)).choose b := by
  let r : Finset V → V → Prop := fun S v => S ⊆ Gᶜ.neighborFinset v
  calc
    (∑ S ∈ U.powersetCard b, #(commonBlueNeighbors G S Q)) =
        ∑ S ∈ U.powersetCard b, #(Q.bipartiteAbove r S) := by
      rfl
    _ = ∑ v ∈ Q, #((U.powersetCard b).bipartiteBelow r v) :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ = ∑ v ∈ Q, (#(Gᶜ.neighborFinset v ∩ U)).choose b := by
      apply Finset.sum_congr rfl
      intro v hv
      change #((U.powersetCard b).filter fun S => S ⊆ Gᶜ.neighborFinset v) = _
      exact card_powersetCard_below U (Gᶜ.neighborFinset v) b

omit [Fintype V] [DecidableEq V] in
private theorem card_mul_chooseReal_average_le_sum_choose
    (Q : Finset V) (p : V → ℕ) {b : ℕ} (hb : b ≠ 0) (hQ : Q.Nonempty)
    (havg : (b - 1 : ℝ) ≤ (∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ)) :
    (#Q : ℝ) * chooseReal ((∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ)) b ≤
      ∑ v ∈ Q, ((p v).choose b : ℝ) := by
  have hQpos : (0 : ℝ) < #Q := by exact_mod_cast hQ.card_pos
  have hw₀ : ∀ v ∈ Q, (0 : ℝ) ≤ 1 / (#Q : ℝ) := by
    intro v hv
    positivity
  have hw₁ : ∑ v ∈ Q, (1 / (#Q : ℝ)) = 1 := by
    simp [hQ.card_ne_zero]
  have havg_eq :
      (∑ v ∈ Q, (1 / (#Q : ℝ)) * p v) =
        (∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ) := by
    calc
      (∑ v ∈ Q, (1 / (#Q : ℝ)) * p v) =
          ∑ v ∈ Q, (p v : ℝ) / (#Q : ℝ) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = (∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ) :=
        (Finset.sum_div Q (fun v => (p v : ℝ)) (#Q : ℝ)).symm
  have havg' :
      (b - 1 : ℝ) ≤ ∑ v ∈ Q, (1 / (#Q : ℝ)) * p v := by
    rwa [havg_eq]
  have hJ := chooseReal_le_weighted_sum hb p (fun _ => 1 / (#Q : ℝ))
    hw₀ hw₁ havg'
  calc
    (#Q : ℝ) * chooseReal ((∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ)) b =
        (#Q : ℝ) * chooseReal
          (∑ v ∈ Q, (1 / (#Q : ℝ)) * p v) b := by
      congr 2
      exact havg_eq.symm
    _ ≤ (#Q : ℝ) * ∑ v ∈ Q,
          (1 / (#Q : ℝ)) * ((p v).choose b : ℝ) :=
      mul_le_mul_of_nonneg_left hJ hQpos.le
    _ = ∑ v ∈ Q, ((p v).choose b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      field_simp

private theorem exists_commonBlueNeighbors_card_ge
    {U Q : Finset V} {b m : ℕ}
    (hU : U.Nonempty) (hQ : Q.Nonempty) (hUcard : #U = m)
    (hb : 0 < b) (hbm : b ≤ m)
    (hσ : 0 < redDensity Gᶜ U Q)
    (hsq : 5 * (b : ℝ) ^ 2 ≤ redDensity Gᶜ U Q * (m : ℝ)) :
    ∃ S ∈ U.powersetCard b,
      (4 / 5 : ℝ) * (redDensity Gᶜ U Q) ^ b * (#Q : ℝ) ≤
        (#(commonBlueNeighbors G S Q) : ℝ) := by
  let p : V → ℕ := fun v => #(Gᶜ.neighborFinset v ∩ U)
  let σ : ℝ := redDensity Gᶜ U Q
  have hsumDegree :
      (∑ v ∈ Q, (p v : ℝ)) = σ * ((#U : ℝ) * (#Q : ℝ)) := by
    dsimp [p, σ]
    rw [← Nat.cast_sum,
      ← redInteredgeCount_eq_sum_card_neighborFinset_inter_right]
    exact (redDensity_mul_card hU hQ).symm
  have hQpos : (0 : ℝ) < #Q := by exact_mod_cast hQ.card_pos
  have havgEq :
      (∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ) = σ * (m : ℝ) := by
    rw [hsumDegree, hUcard]
    field_simp
  have havgLower :
      (b - 1 : ℝ) ≤ (∑ v ∈ Q, (p v : ℝ)) / (#Q : ℝ) := by
    rw [havgEq]
    have hbcast : (1 : ℝ) ≤ b := by exact_mod_cast hb
    dsimp [σ] at ⊢
    nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hJensen := card_mul_chooseReal_average_le_sum_choose
    Q p hb.ne' hQ havgLower
  rw [havgEq] at hJensen
  have hbinomial :
      (4 / 5 : ℝ) * σ ^ b * (m.choose b : ℝ) ≤
        chooseReal (σ * (m : ℝ)) b := by
    apply chooseReal_lower_bound_four_fifths
    · exact hσ
    · dsimp [σ]
      exact redDensity_le_one U Q
    · exact hb
    · exact hUcard ▸ hU.card_pos
    · simpa [σ] using hsq
  have htotal :
      ((m.choose b : ℕ) : ℝ) *
          ((4 / 5 : ℝ) * σ ^ b * (#Q : ℝ)) ≤
        ∑ v ∈ Q, ((p v).choose b : ℝ) := by
    calc
      ((m.choose b : ℕ) : ℝ) *
          ((4 / 5 : ℝ) * σ ^ b * (#Q : ℝ)) =
          (#Q : ℝ) * ((4 / 5 : ℝ) * σ ^ b * (m.choose b : ℝ)) := by ring
      _ ≤ (#Q : ℝ) * chooseReal (σ * (m : ℝ)) b :=
        mul_le_mul_of_nonneg_left hbinomial hQpos.le
      _ ≤ ∑ v ∈ Q, ((p v).choose b : ℝ) := hJensen
  have hdouble :
      (∑ S ∈ U.powersetCard b, (#(commonBlueNeighbors G S Q) : ℝ)) =
        ∑ v ∈ Q, ((p v).choose b : ℝ) := by
    exact_mod_cast sum_card_commonBlueNeighbors (G := G) U Q b
  have hsum :
      (∑ S ∈ U.powersetCard b,
          (4 / 5 : ℝ) * σ ^ b * (#Q : ℝ)) ≤
        ∑ S ∈ U.powersetCard b, (#(commonBlueNeighbors G S Q) : ℝ) := by
    rw [hdouble]
    simpa [Finset.card_powersetCard, hUcard] using htotal
  obtain ⟨S, hSP, hS⟩ :=
    Finset.exists_le_of_sum_le
      (Finset.powersetCard_nonempty.mpr (by simpa [hUcard] using hbm)) hsum
  exact ⟨S, hSP, by simpa [σ] using hS⟩

set_option maxHeartbeats 800000 in
/-- Paper Lemma `l:BBook`, with the unused candidate right side omitted and
the extracted spine strengthened from `b ≤ #S` to `#S = b`. The paper's
inverse-density size assumption is written in the equivalent cross-multiplied
form `10b² ≤ μm`. -/
theorem exists_redClique_or_blueBook
    {X : Finset V} {μ : ℝ} {b k m : ℕ}
    (hμ₀ : 0 < μ) (hμ₁ : μ < 1)
    (hb : 0 < b) (_hk : 0 < k) (hm : 0 < m)
    (hscale : 10 * (b : ℝ) ^ 2 ≤ μ * (m : ℝ))
    (hXcard : 5 * m ^ 2 ≤ #X)
    (hmany : ramseyNumber k m ≤ #(highBlueVertices G X μ)) :
    hasRedClique G X k ∨
      ∃ S T : Finset V,
        BlueBook G S T ∧ S ∪ T ⊆ X ∧ #S = b ∧
          (μ ^ b / 2) * (#X : ℝ) ≤ (#T : ℝ) := by
  let W : Finset V := highBlueVertices G X μ
  have hWsub : W ⊆ X := by
    intro v hv
    exact (Finset.mem_filter.1 hv).1
  rcases ((ramseyNumber_spec k m).mono hmany).on_finset G W rfl with
    hred | hblue
  · exact Or.inl (hasRedClique_mono hWsub hred)
  right
  rcases hblue with ⟨U, hUW, hUclique⟩
  have hUX : U ⊆ X := hUW.trans hWsub
  have hUcard : #U = m := hUclique.card_eq
  have hU : U.Nonempty := by
    apply Finset.card_pos.mp
    rw [hUcard]
    exact hm
  let Q : Finset V := X \ U
  have hXcardReal : (5 : ℝ) * (m : ℝ) ^ 2 ≤ (#X : ℝ) := by
    exact_mod_cast hXcard
  have hm_lt_X : m < #X := by
    nlinarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm]
  have hUcard_lt_X : #U < #X := by simpa [hUcard] using hm_lt_X
  have hQ : Q.Nonempty := by
    exact Finset.sdiff_nonempty_of_card_lt_card hUcard_lt_X
  have hQcard : (#Q : ℝ) = (#X : ℝ) - (m : ℝ) := by
    dsimp [Q]
    rw [Finset.card_sdiff_of_subset hUX,
      Nat.cast_sub (Finset.card_mono hUX), hUcard]
  have hm_le_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    nlinarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm]
  have hfive_m : (5 : ℝ) * (m : ℝ) ≤ (#X : ℝ) := by
    nlinarith
  have hQlarge : (4 / 5 : ℝ) * (#X : ℝ) ≤ (#Q : ℝ) := by
    rw [hQcard]
    nlinarith
  let σ : ℝ := redDensity Gᶜ U Q
  have hdegreeQ : ∀ u ∈ U,
      μ * (#X : ℝ) - (m : ℝ) ≤
        (#(Gᶜ.neighborFinset u ∩ Q) : ℝ) := by
    intro u hu
    have huW : u ∈ W := hUW hu
    have huHigh :
        μ * (#X : ℝ) ≤ (#(Gᶜ.neighborFinset u ∩ X) : ℝ) :=
      (Finset.mem_filter.1 huW).2
    have hcardNat :
        #(Gᶜ.neighborFinset u ∩ X) ≤
          #(Gᶜ.neighborFinset u ∩ Q) + #U := by
      have h := Finset.card_le_card_sdiff_add_card
        (s := Gᶜ.neighborFinset u ∩ X) (t := U)
      rw [Finset.inter_sdiff_assoc] at h
      simpa [Q] using h
    have hcardReal :
        (#(Gᶜ.neighborFinset u ∩ X) : ℝ) ≤
          (#(Gᶜ.neighborFinset u ∩ Q) : ℝ) + (m : ℝ) := by
      exact_mod_cast hUcard ▸ hcardNat
    linarith
  have hsumLower :
      (m : ℝ) * (μ * (#X : ℝ) - (m : ℝ)) ≤
        ∑ u ∈ U, (#(Gᶜ.neighborFinset u ∩ Q) : ℝ) := by
    calc
      (m : ℝ) * (μ * (#X : ℝ) - (m : ℝ)) =
          ∑ u ∈ U, (μ * (#X : ℝ) - (m : ℝ)) := by
        simp [hUcard]
        ring
      _ ≤ ∑ u ∈ U, (#(Gᶜ.neighborFinset u ∩ Q) : ℝ) := by
        exact Finset.sum_le_sum fun u hu => hdegreeQ u hu
  have hsumDensity :
      (∑ u ∈ U, (#(Gᶜ.neighborFinset u ∩ Q) : ℝ)) =
        σ * ((m : ℝ) * (#Q : ℝ)) := by
    dsimp [σ]
    rw [← Nat.cast_sum,
      ← redInteredgeCount_eq_sum_card_neighborFinset_inter]
    simpa [hUcard] using (redDensity_mul_card (G := Gᶜ) hU hQ).symm
  have hμX_sub_m_le :
      μ * (#X : ℝ) - (m : ℝ) ≤ σ * (#Q : ℝ) := by
    rw [hsumDensity] at hsumLower
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith
  have hσnonneg : 0 ≤ σ := by
    dsimp [σ]
    exact redDensity_nonneg U Q
  have hQleX : (#Q : ℝ) ≤ (#X : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : Q ⊆ X)
  have hμX_sub_m_le' :
      μ * (#X : ℝ) - (m : ℝ) ≤ σ * (#X : ℝ) := by
    exact hμX_sub_m_le.trans (mul_le_mul_of_nonneg_left hQleX hσnonneg)
  have hbReal : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_le_μm : (b : ℝ) ≤ μ * (m : ℝ) := by
    nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hfive_bm :
      (5 : ℝ) * (b : ℝ) * (m : ℝ) ≤ μ * (#X : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hb_le_μm
      (show (0 : ℝ) ≤ 5 * (m : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hXcardReal hμ₀.le
    nlinarith
  have hXpos : (0 : ℝ) < #X := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 5 * m ^ 2) hXcard)
  have hdenomPos : (0 : ℝ) < 5 * (b : ℝ) := by positivity
  have hm_le_fraction :
      (m : ℝ) ≤ μ * (#X : ℝ) / (5 * (b : ℝ)) := by
    rw [le_div_iff₀ hdenomPos]
    nlinarith
  have hfactor_mul :
      μ * (1 - 1 / (5 * (b : ℝ))) * (#X : ℝ) ≤
        μ * (#X : ℝ) - (m : ℝ) := by
    calc
      μ * (1 - 1 / (5 * (b : ℝ))) * (#X : ℝ) =
          μ * (#X : ℝ) - μ * (#X : ℝ) / (5 * (b : ℝ)) := by ring
      _ ≤ μ * (#X : ℝ) - (m : ℝ) := by linarith
  have hσstrong : μ * (1 - 1 / (5 * (b : ℝ))) ≤ σ := by
    apply le_of_mul_le_mul_right _ hXpos
    simpa [mul_comm] using hfactor_mul.trans hμX_sub_m_le'
  have hlinearFactor : (4 / 5 : ℝ) ≤ 1 - 1 / (5 * (b : ℝ)) := by
    have hfive_le : (5 : ℝ) ≤ 5 * (b : ℝ) := by nlinarith
    have hinv : 1 / (5 * (b : ℝ)) ≤ (1 / 5 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hfive_le
    nlinarith
  have hσpos : 0 < σ := by
    have : 0 < μ * (1 - 1 / (5 * (b : ℝ))) :=
      mul_pos hμ₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4 / 5) hlinearFactor)
    exact this.trans_le hσstrong
  have hσhalf : μ / 2 ≤ σ := by
    calc
      μ / 2 ≤ μ * (4 / 5 : ℝ) := by nlinarith
      _ ≤ μ * (1 - 1 / (5 * (b : ℝ))) :=
        mul_le_mul_of_nonneg_left hlinearFactor hμ₀.le
      _ ≤ σ := hσstrong
  have hsq : 5 * (b : ℝ) ^ 2 ≤ σ * (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hσhalf
      (show (0 : ℝ) ≤ (m : ℝ) by positivity)
    nlinarith
  have hbm : b ≤ m := by
    exact_mod_cast hb_le_μm.trans
      (mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ m) hμ₁.le)
  obtain ⟨S, hSP, hSlarge⟩ :=
    exists_commonBlueNeighbors_card_ge (G := G) hU hQ hUcard hb hbm hσpos
      (by simpa [σ] using hsq)
  have hSP' := Finset.mem_powersetCard.1 hSP
  let T : Finset V := commonBlueNeighbors G S Q
  have hBernoulli :
      (4 / 5 : ℝ) ≤ (1 - 1 / (5 * (b : ℝ))) ^ b := by
    have hinvLeOne : 1 / (5 * (b : ℝ)) ≤ 1 := by
      rw [div_le_one hdenomPos]
      nlinarith
    have ha : (-2 : ℝ) ≤ -(1 / (5 * (b : ℝ))) := by linarith
    have h := one_add_mul_le_pow ha b
    calc
      (4 / 5 : ℝ) =
          1 + (b : ℝ) * (-(1 / (5 * (b : ℝ)))) := by
        field_simp
        ring
      _ ≤ (1 + -(1 / (5 * (b : ℝ)))) ^ b := h
      _ = (1 - 1 / (5 * (b : ℝ))) ^ b := by ring
  have hpowStrong :
      μ ^ b * (4 / 5 : ℝ) ≤ σ ^ b := by
    calc
      μ ^ b * (4 / 5 : ℝ) ≤
          μ ^ b * (1 - 1 / (5 * (b : ℝ))) ^ b :=
        mul_le_mul_of_nonneg_left hBernoulli (pow_nonneg hμ₀.le b)
      _ = (μ * (1 - 1 / (5 * (b : ℝ)))) ^ b := by rw [mul_pow]
      _ ≤ σ ^ b :=
        pow_le_pow_left₀
          (mul_nonneg hμ₀.le (le_trans (by norm_num) hlinearFactor)) hσstrong b
  have htarget :
      (μ ^ b / 2) * (#X : ℝ) ≤
        (4 / 5 : ℝ) * σ ^ b * (#Q : ℝ) := by
    have hnonneg : 0 ≤ μ ^ b * (#X : ℝ) :=
      mul_nonneg (pow_nonneg hμ₀.le b) (by positivity)
    calc
      (μ ^ b / 2) * (#X : ℝ) ≤
          (4 / 5 : ℝ) * (μ ^ b * (4 / 5 : ℝ)) *
            ((4 / 5 : ℝ) * (#X : ℝ)) := by
        nlinarith
      _ ≤ (4 / 5 : ℝ) * σ ^ b * (#Q : ℝ) := by gcongr
  refine ⟨S, T, ?_, Finset.union_subset ?_ ?_, hSP'.2, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact hUclique.isClique.subset (Finset.coe_subset.mpr hSP'.1)
    · intro s hs t ht
      have ht' := (Finset.mem_filter.1 ht).2
      exact ((Gᶜ.mem_neighborFinset t s).1 (ht' hs)).symm
  · exact hSP'.1.trans hUX
  · exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
  · exact htarget.trans (by simpa [σ, T] using hSlarge)

end Finite

end RamseyLean
