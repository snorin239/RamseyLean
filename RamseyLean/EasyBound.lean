import RamseyLean.Candidate
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The elementary Ramsey bound

This module formalizes the short density-increment argument in the paper from
Lemma `l:FpAvg` through Corollary `c:easy`.  The probabilistic bipartition in
the printed proof is represented by a deterministic weighted-cut averaging
lemma.
-/

set_option autoImplicit false

namespace RamseyLean

open scoped Finset

universe u

section ExcessAverage

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V} {p : ℝ}

private theorem sum_sum_neighbor_inter (f : V → ℝ) :
    ∑ v ∈ X, ∑ y ∈ G.neighborFinset v ∩ Y, f y =
      ∑ y ∈ Y, (#(G.neighborFinset y ∩ X) : ℝ) * f y := by
  classical
  calc
    ∑ v ∈ X, ∑ y ∈ G.neighborFinset v ∩ Y, f y =
        ∑ v ∈ X, ∑ y ∈ Y, if G.Adj v y then f y else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [show G.neighborFinset v ∩ Y = Y.filter (G.Adj v) by
            ext y
            simp [and_comm]]
          exact Finset.sum_filter _ _
    _ = ∑ y ∈ Y, ∑ v ∈ X, if G.Adj v y then f y else 0 :=
      Finset.sum_comm
    _ = ∑ y ∈ Y, ∑ v ∈ G.neighborFinset y ∩ X, f y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [show G.neighborFinset y ∩ X = X.filter (fun v => G.Adj v y) by
        ext v
        simp [G.adj_comm, and_comm]]
      exact (Finset.sum_filter _ _).symm
    _ = ∑ y ∈ Y, (#(G.neighborFinset y ∩ X) : ℝ) * f y := by
      apply Finset.sum_congr rfl
      intro y hy
      simp

private theorem excess_eq_sum_card_neighborFinset_inter_sub
    (p : ℝ) (X Y : Finset V) :
    excess G p X Y =
      ∑ y ∈ Y,
        ((#(G.neighborFinset y ∩ X) : ℝ) - p * (#X : ℝ)) := by
  rw [excess, redInteredgeCount_eq_sum_card_neighborFinset_inter_right]
  have hcast :
      ((↑(∑ y ∈ Y, #(G.neighborFinset y ∩ X)) : ℝ)) =
        ∑ y ∈ Y, (#(G.neighborFinset y ∩ X) : ℝ) := by
    exact map_sum (Nat.castAddMonoidHom ℝ)
      (fun y => #(G.neighborFinset y ∩ X)) Y
  rw [hcast]
  simp [Finset.sum_sub_distrib]
  ring

/-- Paper Lemma `l:FpAvg`: restricting the right side to red neighborhoods
preserves at least a `p` fraction of excess on average. -/
theorem sum_excess_redNeighborhood_ge
    (_h : Candidate G X Y) (_hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y) ≥
      p * (#X : ℝ) * excess G p X Y := by
  clear _h _hp
  calc
    ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y) =
        ∑ v ∈ X, ∑ y ∈ G.neighborFinset v ∩ Y,
          ((#(G.neighborFinset y ∩ X) : ℝ) - p * (#X : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact excess_eq_sum_card_neighborFinset_inter_sub
        p X (G.neighborFinset v ∩ Y)
    _ = ∑ y ∈ Y, (#(G.neighborFinset y ∩ X) : ℝ) *
          ((#(G.neighborFinset y ∩ X) : ℝ) - p * (#X : ℝ)) :=
      sum_sum_neighbor_inter _
    _ ≥ ∑ y ∈ Y, (p * (#X : ℝ)) *
          ((#(G.neighborFinset y ∩ X) : ℝ) - p * (#X : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      let a : ℝ := (#(G.neighborFinset y ∩ X) : ℝ) - p * (#X : ℝ)
      calc
        p * (#X : ℝ) * a ≤ p * (#X : ℝ) * a + a ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg a)
        _ = (#(G.neighborFinset y ∩ X) : ℝ) * a := by
          dsimp [a]
          ring
    _ = p * (#X : ℝ) *
          (∑ y ∈ Y,
            ((#(G.neighborFinset y ∩ X) : ℝ) - p * (#X : ℝ))) := by
      induction Y using Finset.induction_on with
      | empty => simp
      | @insert y Y hy ih =>
          rw [Finset.sum_insert hy, Finset.sum_insert hy, ih]
          ring
    _ = p * (#X : ℝ) * excess G p X Y := by
      rw [excess_eq_sum_card_neighborFinset_inter_sub]

end ExcessAverage

private theorem ramseyNumber_recurrence_succ_succ (k ℓ : ℕ) :
    ramseyNumber (k + 2) (ℓ + 2) ≤
      ramseyNumber (k + 1) (ℓ + 2) + ramseyNumber (k + 2) (ℓ + 1) := by
  apply ramseyNumber_le
  exact (ramseyNumber_spec (k + 1) (ℓ + 2)).recurrence
    (ramseyNumber_spec (k + 2) (ℓ + 1))

private theorem ramseyNumber_le_erdosSzekeres_succ
    {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∀ k ℓ : ℕ,
      (ramseyNumber (k + 1) (ℓ + 1) : ℝ) ≤
        (x⁻¹) ^ k * ((1 - x)⁻¹) ^ ℓ := by
  intro k
  induction k with
  | zero =>
      intro ℓ
      have hnat : ramseyNumber 1 (ℓ + 1) ≤ 1 :=
        ramseyNumber_le (ramseyBound_one_left (ℓ + 1))
      have hcast : (ramseyNumber 1 (ℓ + 1) : ℝ) ≤ 1 := by
        exact_mod_cast hnat
      have hsubpos : 0 < 1 - x := sub_pos.mpr hx₁
      have hinv : 1 ≤ (1 - x)⁻¹ :=
        (one_le_inv₀ hsubpos).2 (by linarith)
      calc
        (ramseyNumber (0 + 1) (ℓ + 1) : ℝ) ≤ 1 := hcast
        _ ≤ (x⁻¹) ^ 0 * ((1 - x)⁻¹) ^ ℓ := by
          simpa using one_le_pow₀ hinv
  | succ k ihk =>
      intro ℓ
      induction ℓ with
      | zero =>
          have hnat : ramseyNumber (k + 1 + 1) 1 ≤ 1 :=
            ramseyNumber_le (ramseyBound_one_right (k + 1 + 1))
          have hcast : (ramseyNumber (k + 1 + 1) 1 : ℝ) ≤ 1 := by
            exact_mod_cast hnat
          have hinv : 1 ≤ x⁻¹ :=
            (one_le_inv₀ hx₀).2 (le_of_lt hx₁)
          calc
            (ramseyNumber (k + 1 + 1) (0 + 1) : ℝ) ≤ 1 := hcast
            _ ≤ (x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ 0 := by
              simpa using one_le_pow₀ hinv
      | succ ℓ ihℓ =>
          have hrec := ramseyNumber_recurrence_succ_succ k ℓ
          have hrec' :
              (ramseyNumber (k + 2) (ℓ + 2) : ℝ) ≤
                (ramseyNumber (k + 1) (ℓ + 2) : ℝ) +
                  (ramseyNumber (k + 2) (ℓ + 1) : ℝ) := by
            exact_mod_cast hrec
          calc
            (ramseyNumber (k + 1 + 1) (ℓ + 1 + 1) : ℝ) ≤
                (ramseyNumber (k + 1) (ℓ + 2) : ℝ) +
                  (ramseyNumber (k + 2) (ℓ + 1) : ℝ) := by
              simpa [Nat.add_assoc] using hrec'
            _ ≤ (x⁻¹) ^ k * ((1 - x)⁻¹) ^ (ℓ + 1) +
                  (x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ :=
              add_le_add (ihk (ℓ + 1)) ihℓ
            _ = (x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ (ℓ + 1) := by
              rw [pow_succ (x⁻¹) k, pow_succ ((1 - x)⁻¹) ℓ]
              field_simp [ne_of_gt hx₀, ne_of_gt (sub_pos.mpr hx₁)]
              ring

/-- Paper Observation `o:easybound`: the weighted Erdős--Szekeres bound. -/
theorem ramseyBound_erdosSzekeres
    {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1)
    {k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    (ramseyNumber k ℓ : ℝ) ≤
      (x⁻¹) ^ (k - 1) * ((1 - x)⁻¹) ^ (ℓ - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ.ne'
  simpa [Nat.succ_eq_add_one] using
    ramseyNumber_le_erdosSzekeres_succ hx₀ hx₁ k ℓ

/-- The threshold appearing in Lemma `l:easy`. -/
noncomputable def easyCandidateThreshold
    (x p : ℝ) (k ℓ t : ℕ) : ℝ :=
  ((k + t : ℕ) : ℝ) * (x⁻¹) ^ (k - 1) *
    ((1 - x)⁻¹) ^ (ℓ - 1) * ((p - x)⁻¹) ^ (t - 1)

private noncomputable def easyWeight
    (x p : ℝ) (k ℓ t : ℕ) : ℝ :=
  (((k + 1) + (t + 1) : ℕ) : ℝ) *
    (x⁻¹) ^ k * ((1 - x)⁻¹) ^ ℓ * ((p - x)⁻¹) ^ t

private def AverageSelection {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) : Prop :=
  ∀ (X Y : Finset V), Candidate G X Y →
    ∃ v ∈ X,
      p * excess G p X Y ≤
        excess G p X (G.neighborFinset v ∩ Y)

private theorem averageSelection_of_sum_excess_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : ℝ}
    (havg : ∀ (X Y : Finset V), Candidate G X Y →
      p * (#X : ℝ) * excess G p X Y ≤
        ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y)) :
    AverageSelection G p := by
  intro X Y hC
  have hsum :
      ∑ _v ∈ X, p * excess G p X Y ≤
        ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y) := by
    calc
      ∑ _v ∈ X, p * excess G p X Y =
          p * (#X : ℝ) * excess G p X Y := by
        simp
        ring
      _ ≤ ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y) :=
        havg X Y hC
  obtain ⟨v, hv, hvavg⟩ := Finset.exists_le_of_sum_le hC.left_nonempty hsum
  exact ⟨v, hv, hvavg⟩

private theorem isGood_of_easyWeight_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x p : ℝ} (hx₀ : 0 < x) (hxp : x < p) (hp₁ : p < 1)
    (hselect : AverageSelection G p) :
    ∀ (k ℓ t : ℕ) (X Y : Finset V),
      Candidate G X Y →
      easyWeight x p k ℓ t ≤ excess G p X Y →
      Candidate.IsGood G X Y (k + 1) (ℓ + 1) (t + 1) := by
  intro k
  induction k with
  | zero =>
      intro ℓ t X Y hC _
      simpa using hC.isGood_one_red (ℓ + 1) (t + 1)
  | succ k ihk =>
      intro ℓ t
      induction t with
      | zero =>
          intro X Y hC _
          simpa using hC.isGood_one_blue_left (k + 1 + 1) (ℓ + 1)
      | succ t iht =>
          intro X Y hC hlarge
          obtain ⟨v, hv, havg⟩ := hselect X Y hC
          let Y' := G.neighborFinset v ∩ Y
          let XR := G.neighborFinset v ∩ X
          let XB := Gᶜ.neighborFinset v ∩ X
          have hY'sub : Y' ⊆ Y := Finset.inter_subset_right
          have hXRsub : XR ⊆ X := Finset.inter_subset_right
          have hXBsub : XB ⊆ X := Finset.inter_subset_right
          have hY'neighbor : Y' ⊆ G.neighborFinset v := Finset.inter_subset_left
          have hXRneighbor : XR ⊆ G.neighborFinset v := Finset.inter_subset_left
          have hXBneighbor : XB ⊆ Gᶜ.neighborFinset v := Finset.inter_subset_left
          by_cases hred :
              easyWeight x p k ℓ (t + 1) ≤ excess G p XR Y'
          · have hredWeightPos : 0 < easyWeight x p k ℓ (t + 1) := by
              unfold easyWeight
              exact mul_pos
                (mul_pos
                  (mul_pos (by positivity) (pow_pos (inv_pos.mpr hx₀) _))
                  (pow_pos (inv_pos.mpr (by linarith)) _))
                (pow_pos (inv_pos.mpr (sub_pos.mpr hxp)) _)
            have hredExcessPos : 0 < excess G p XR Y' :=
              lt_of_lt_of_le hredWeightPos hred
            have hsub : Candidate G XR Y' :=
              hC.subcandidate_of_excess_pos hXRsub hY'sub hredExcessPos
            have hgood := ihk ℓ (t + 1) XR Y' hsub hred
            have hlift := Candidate.IsGood.of_red_extension hgood
              (Finset.union_subset hXRneighbor hY'neighbor) hXRsub hY'sub hv
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlift
          · by_cases hblue :
                easyWeight x p (k + 1) ℓ t ≤ excess G p XB Y'
            · have hblueWeightPos : 0 < easyWeight x p (k + 1) ℓ t := by
                unfold easyWeight
                exact mul_pos
                  (mul_pos
                    (mul_pos (by positivity) (pow_pos (inv_pos.mpr hx₀) _))
                    (pow_pos (inv_pos.mpr (by linarith)) _))
                  (pow_pos (inv_pos.mpr (sub_pos.mpr hxp)) _)
              have hblueExcessPos : 0 < excess G p XB Y' :=
                lt_of_lt_of_le hblueWeightPos hblue
              have hsub : Candidate G XB Y' :=
                hC.subcandidate_of_excess_pos hXBsub hY'sub hblueExcessPos
              have hgood := iht XB Y' hsub hblue
              have hlift := Candidate.IsGood.of_blue_extension_left hgood
                hXBneighbor hXBsub hY'sub hv
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlift
            · have hqpos : 0 < 1 - x := by linarith
              have hrpos : 0 < p - x := sub_pos.mpr hxp
              have hp₀ : 0 ≤ p := le_of_lt (hx₀.trans hxp)
              have hredlt :
                  excess G p XR Y' < easyWeight x p k ℓ (t + 1) :=
                lt_of_not_ge hred
              have hbluelt :
                  excess G p XB Y' < easyWeight x p (k + 1) ℓ t :=
                lt_of_not_ge hblue
              have hdisjRB : Disjoint XR XB := by
                rw [Finset.disjoint_left]
                intro u huR huB
                simp only [XR, XB, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
                  SimpleGraph.compl_adj] at huR huB
                exact huB.1.2 huR.1
              have hdisjV : Disjoint (XR ∪ XB) {v} := by
                rw [Finset.disjoint_singleton_right]
                simp [XR, XB]
              have hpart : (XR ∪ XB) ∪ {v} = X := by
                ext u
                simp [XR, XB, SimpleGraph.compl_adj]
                constructor
                · rintro (rfl | hredMem | hblueMem)
                  · exact hv
                  · exact hredMem.2
                  · exact hblueMem.2
                · intro hu
                  by_cases huv : u = v
                  · exact Or.inl huv
                  · by_cases huvred : G.Adj v u
                    · exact Or.inr (Or.inl ⟨huvred, hu⟩)
                    · exact Or.inr (Or.inr ⟨⟨Ne.symm huv, huvred⟩, hu⟩)
              have hdecomp :
                  excess G p X Y' =
                    excess G p XR Y' + excess G p XB Y' + excess G p {v} Y' := by
                rw [← hpart, excess_union_left hdisjV,
                  excess_union_left hdisjRB]
              have hsingle : excess G p {v} Y' ≤ (#Y : ℝ) := by
                have hcountNat := redInteredgeCount_le_mul (G := G) {v} Y'
                have hcount : (redInteredgeCount G {v} Y' : ℝ) ≤ (#Y' : ℝ) := by
                  norm_num at hcountNat ⊢
                  exact_mod_cast hcountNat
                have hcardNat : #Y' ≤ #Y := Finset.card_le_card hY'sub
                have hcard : (#Y' : ℝ) ≤ (#Y : ℝ) := by
                  exact_mod_cast hcardNat
                rw [excess]
                simp only [Finset.card_singleton, Nat.cast_one]
                have hmul : 0 ≤ p * (#Y' : ℝ) :=
                  mul_nonneg hp₀ (Nat.cast_nonneg _)
                linarith
              have havg' :
                  p * excess G p X Y ≤ excess G p X Y' := by
                simpa [Y'] using havg
              have hparent :
                  p * easyWeight x p (k + 1) ℓ (t + 1) ≤
                    p * excess G p X Y :=
                mul_le_mul_of_nonneg_left hlarge hp₀
              have hchain :
                  p * easyWeight x p (k + 1) ℓ (t + 1) <
                    easyWeight x p k ℓ (t + 1) +
                      easyWeight x p (k + 1) ℓ t + (#Y : ℝ) := by
                linarith [hdecomp]
              have hweightIdentity :
                  p * easyWeight x p (k + 1) ℓ (t + 1) -
                      (easyWeight x p k ℓ (t + 1) +
                        easyWeight x p (k + 1) ℓ t) =
                    p * ((x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ *
                      ((p - x)⁻¹) ^ (t + 1)) := by
                simp only [easyWeight]
                push_cast
                rw [pow_succ (x⁻¹) k, pow_succ ((p - x)⁻¹) t]
                field_simp [ne_of_gt hx₀, ne_of_gt hqpos, ne_of_gt hrpos]
                ring
              have hbaseLt :
                  p * ((x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ *
                    ((p - x)⁻¹) ^ (t + 1)) < (#Y : ℝ) := by
                linarith
              have hinvr : 1 ≤ (p - x)⁻¹ :=
                (one_le_inv₀ hrpos).2 (by linarith)
              have hpinvr : 1 ≤ p * (p - x)⁻¹ := by
                rw [le_mul_inv_iff₀ hrpos]
                linarith
              have hfactor : 1 ≤ p * ((p - x)⁻¹) ^ (t + 1) := by
                have hpow : 1 ≤ ((p - x)⁻¹) ^ t := one_le_pow₀ hinvr
                have hpowNonneg : 0 ≤ ((p - x)⁻¹) ^ t :=
                  le_trans (by norm_num) hpow
                calc
                  1 = 1 * 1 := by ring
                  _ ≤ ((p - x)⁻¹) ^ t * (p * (p - x)⁻¹) :=
                    mul_le_mul hpow hpinvr (by norm_num) hpowNonneg
                  _ = p * ((p - x)⁻¹) ^ (t + 1) := by
                    rw [pow_succ]
                    ring
              have htargetNonneg :
                  0 ≤ (x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ := by
                positivity
              have htargetLe :
                  (x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ ≤
                    p * ((x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ *
                      ((p - x)⁻¹) ^ (t + 1)) := by
                calc
                  (x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ =
                      ((x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ) * 1 := by ring
                  _ ≤ ((x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ) *
                      (p * ((p - x)⁻¹) ^ (t + 1)) :=
                    mul_le_mul_of_nonneg_left hfactor htargetNonneg
                  _ = p * ((x⁻¹) ^ (k + 1) * ((1 - x)⁻¹) ^ ℓ *
                      ((p - x)⁻¹) ^ (t + 1)) := by ring
              have hES :=
                ramseyNumber_le_erdosSzekeres_succ hx₀
                  (hxp.trans hp₁) (k + 1) ℓ
              have hramseyReal :
                  (ramseyNumber (k + 1 + 1) (ℓ + 1) : ℝ) < (#Y : ℝ) :=
                lt_of_le_of_lt hES (lt_of_le_of_lt htargetLe hbaseLt)
              have hramseyNat : ramseyNumber (k + 1 + 1) (ℓ + 1) ≤ #Y := by
                have : ramseyNumber (k + 1 + 1) (ℓ + 1) < #Y := by
                  exact_mod_cast hramseyReal
                omega
              exact Candidate.IsGood.of_ramseyNumber_le_card_right hramseyNat

/-- Paper Lemma `l:easy`: a candidate with sufficiently large excess is
`(k,ℓ,t)`-good. -/
theorem Candidate.isGood_of_excess_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {X Y : Finset V} {x p : ℝ} {k ℓ t : ℕ}
    (hC : Candidate G X Y) (hx₀ : 0 < x) (hxp : x < p) (hp₁ : p < 1)
    (hk : 0 < k) (hℓ : 0 < ℓ) (ht : 0 < t)
    (hlarge : easyCandidateThreshold x p k ℓ t ≤ excess G p X Y) :
    Candidate.IsGood G X Y k ℓ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ.ne'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt (hx₀.trans hxp), le_of_lt hp₁⟩
  have hselect : AverageSelection G p :=
    averageSelection_of_sum_excess_ge fun X Y hC =>
      sum_excess_redNeighborhood_ge hC hpIcc
  apply isGood_of_easyWeight_ge hx₀ hxp hp₁ hselect k ℓ t X Y hC
  simpa [easyCandidateThreshold, easyWeight, Nat.succ_eq_add_one] using hlarge

section WeightedCut

variable {V : Type u} [DecidableEq V]

private def cutWeight (w : V → V → ℝ) (X Y : Finset V) : ℝ :=
  ∑ x ∈ X, ∑ y ∈ Y, w x y

private def orderedWeight (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, w x y

private theorem orderedWeight_insert (w : V → V → ℝ)
    (hsymm : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0)
    {a : V} {S : Finset V} (ha : a ∉ S) :
    orderedWeight w (insert a S) =
      orderedWeight w S + 2 * ∑ x ∈ S, w a x := by
  simp only [orderedWeight, Finset.sum_insert ha]
  rw [Finset.sum_add_distrib]
  simp only [hdiag, zero_add]
  have hswap : (∑ x ∈ S, w x a) = ∑ x ∈ S, w a x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hsymm x a
  rw [hswap]
  ring

private theorem exists_cutWeight_ge (w : V → V → ℝ)
    (hsymm : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0)
    (S : Finset V) :
    ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = S ∧
      orderedWeight w S / 4 ≤ cutWeight w X Y := by
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨∅, ∅, by simp, by simp, by simp [orderedWeight, cutWeight]⟩
  | @insert a S ha ih =>
      obtain ⟨X, Y, hXY, hunion, hbound⟩ := ih
      let A : ℝ := ∑ x ∈ X, w a x
      let B : ℝ := ∑ y ∈ Y, w a y
      have hsum : (∑ z ∈ S, w a z) = A + B := by
        rw [← hunion, Finset.sum_union hXY]
      by_cases hAB : A ≤ B
      · refine ⟨insert a X, Y, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_insert_left]
          refine ⟨?_, hXY⟩
          intro hay
          have : a ∈ S := by rw [← hunion]; exact Finset.mem_union_right X hay
          exact ha this
        · rw [Finset.insert_union, hunion]
        · rw [orderedWeight_insert w hsymm hdiag ha, hsum]
          have hhalf : (A + B) / 2 ≤ B := by linarith
          have hcut : cutWeight w (insert a X) Y = B + cutWeight w X Y := by
            have haX : a ∉ X := by
              intro hax
              apply ha
              rw [← hunion]
              exact Finset.mem_union_left Y hax
            simp [cutWeight, B, haX]
          rw [hcut]
          linarith
      · have hBA : B ≤ A := le_of_not_ge hAB
        refine ⟨X, insert a Y, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_insert_right]
          refine ⟨?_, hXY⟩
          intro hax
          have : a ∈ S := by rw [← hunion]; exact Finset.mem_union_left Y hax
          exact ha this
        · rw [Finset.union_insert, hunion]
        · rw [orderedWeight_insert w hsymm hdiag ha, hsum]
          have hhalf : (A + B) / 2 ≤ A := by linarith
          have hcut : cutWeight w X (insert a Y) = A + cutWeight w X Y := by
            have haY : a ∉ Y := by
              intro hay
              apply ha
              rw [← hunion]
              exact Finset.mem_union_right X hay
            simp only [cutWeight]
            simp_rw [Finset.sum_insert haY]
            rw [Finset.sum_add_distrib]
            have hs : (∑ x ∈ X, w x a) = A := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hsymm x a
            rw [hs]
          rw [hcut]
          linarith

private def graphWeight [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℝ) (x y : V) : ℝ :=
  if x = y then 0 else (if G.Adj x y then 1 else 0) - p

private theorem graphWeight_symm [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℝ) (x y : V) :
    graphWeight G p x y = graphWeight G p y x := by
  by_cases hxy : x = y
  · subst y
    simp [graphWeight]
  · simp [graphWeight, hxy, Ne.symm hxy, G.adj_comm]

private theorem graphWeight_diag [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℝ) (x : V) : graphWeight G p x x = 0 := by
  simp [graphWeight]

private theorem sum_adj_indicator [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (Y : Finset V) :
    (∑ y ∈ Y, if G.Adj x y then (1 : ℝ) else 0) =
      (#(G.neighborFinset x ∩ Y) : ℝ) := by
  rw [show G.neighborFinset x ∩ Y = Y.filter (G.Adj x) by
    ext y
    simp [and_comm]]
  simp

private theorem cutWeight_graphWeight_eq_excess [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ)
    {X Y : Finset V} (hXY : Disjoint X Y) :
    cutWeight (graphWeight G p) X Y = excess G p X Y := by
  have hinner (x : V) (hx : x ∈ X) :
      (∑ y ∈ Y, graphWeight G p x y) =
        (#(G.neighborFinset x ∩ Y) : ℝ) - p * (#Y : ℝ) := by
    calc
      (∑ y ∈ Y, graphWeight G p x y) =
          ∑ y ∈ Y, ((if G.Adj x y then (1 : ℝ) else 0) - p) := by
            apply Finset.sum_congr rfl
            intro y hy
            have hxy : x ≠ y := by
              intro h
              subst y
              exact Finset.disjoint_left.mp hXY hx hy
            simp [graphWeight, hxy]
      _ = (∑ y ∈ Y, if G.Adj x y then (1 : ℝ) else 0) - ∑ _y ∈ Y, p := by
            rw [Finset.sum_sub_distrib]
      _ = (#(G.neighborFinset x ∩ Y) : ℝ) - p * (#Y : ℝ) := by
            rw [sum_adj_indicator]
            simp
            ring
  have hcount :
      (redInteredgeCount G X Y : ℝ) =
        ∑ x ∈ X, (#(G.neighborFinset x ∩ Y) : ℝ) := by
    exact_mod_cast redInteredgeCount_eq_sum_card_neighborFinset_inter
      (G := G) X Y
  simp only [cutWeight]
  calc
    (∑ x ∈ X, ∑ y ∈ Y, graphWeight G p x y) =
        ∑ x ∈ X, ((#(G.neighborFinset x ∩ Y) : ℝ) - p * (#Y : ℝ)) := by
          apply Finset.sum_congr rfl
          exact hinner
    _ = (∑ x ∈ X, (#(G.neighborFinset x ∩ Y) : ℝ)) -
          ∑ _x ∈ X, p * (#Y : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = excess G p X Y := by
          rw [← hcount]
          simp [excess]
          ring

private theorem orderedWeight_graphWeight_eq [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
    orderedWeight (graphWeight G p) (Finset.univ : Finset V) =
      (∑ v : V, (G.degree v : ℝ)) -
        p * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
  have hinner (x : V) :
      (∑ y : V, graphWeight G p x y) =
        (G.degree x : ℝ) - p * ((Fintype.card V : ℝ) - 1) := by
    have hpoint (y : V) :
        graphWeight G p x y =
          (if G.Adj x y then (1 : ℝ) else 0) - p +
            (if x = y then p else 0) := by
      by_cases hxy : x = y
      · subst y
        simp [graphWeight]
      · simp [graphWeight, hxy]
    calc
      (∑ y : V, graphWeight G p x y) =
          ∑ y : V, ((if G.Adj x y then (1 : ℝ) else 0) - p +
            (if x = y then p else 0)) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact hpoint y
      _ = (∑ y : V, if G.Adj x y then (1 : ℝ) else 0) -
            ∑ _y : V, p + ∑ y : V, if x = y then p else 0 := by
              simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (G.degree x : ℝ) - p * ((Fintype.card V : ℝ) - 1) := by
              rw [show (∑ y : V, if G.Adj x y then (1 : ℝ) else 0) =
                  (G.degree x : ℝ) by
                simpa using
                  sum_adj_indicator (G := G) x (Finset.univ : Finset V)]
              simp
              ring
  simp only [orderedWeight, hinner]
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- The deterministic weighted-cut counterpart of the random bipartition in
the proof of `t:easy`. -/
theorem exists_bipartition_excess_ge [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
    ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = Finset.univ ∧
      ((∑ v : V, (G.degree v : ℝ)) -
          p * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) / 4 ≤
        excess G p X Y := by
  obtain ⟨X, Y, hXY, hunion, hcut⟩ :=
    exists_cutWeight_ge (graphWeight G p) (graphWeight_symm G p)
      (graphWeight_diag G p) (Finset.univ : Finset V)
  refine ⟨X, Y, hXY, hunion, ?_⟩
  rw [orderedWeight_graphWeight_eq G p,
    cutWeight_graphWeight_eq_excess G p hXY] at hcut
  exact hcut

end WeightedCut

/-- The auxiliary density parameter `x` used in Theorem `t:easy`. -/
noncomputable def easyX (p : ℝ) : ℝ :=
  (1 + Real.sqrt 5) / 2 * p + (1 - Real.sqrt 5) / 2

/-- The real-valued bound in Theorem `t:easy`. -/
noncomputable def easyRamseyBoundValue (p : ℝ) (k ℓ : ℕ) : ℝ :=
  4 * ((k + ℓ : ℕ) : ℝ) * easyX p ^ (-(k : ℝ) / 2) *
    ((1 - p)⁻¹) ^ ℓ

private theorem sqrtFive_gt_one : (1 : ℝ) < Real.sqrt 5 := by
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  nlinarith

private theorem easyX_parameters {p : ℝ}
    (hp₀ : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p)
    (hp₁ : p < 1) :
    0 < easyX p ∧ easyX p < p ∧ p < 1 := by
  have hspos : 0 < Real.sqrt 5 + 1 := by positivity
  have hs1 : 1 < Real.sqrt 5 := sqrtFive_gt_one
  have hxpos : 0 < easyX p := by
    rw [easyX]
    rw [div_lt_iff₀ hspos] at hp₀
    have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith
  have hxp : easyX p < p := by
    rw [easyX]
    have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  exact ⟨hxpos, hxp, hp₁⟩

private theorem easyX_product_identity {p : ℝ} :
    (1 - easyX p) * (p - easyX p) = (1 - p) ^ 2 := by
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [easyX]
  nlinarith

private theorem easyRamseyBoundValue_pos {p : ℝ} {k ℓ : ℕ}
    (hx : 0 < easyX p) (hp : p < 1) (hkℓ : 0 < k + ℓ) :
    0 < easyRamseyBoundValue p k ℓ := by
  unfold easyRamseyBoundValue
  exact mul_pos
    (mul_pos (mul_pos (by positivity) (by exact_mod_cast hkℓ))
      (Real.rpow_pos_of_pos hx _))
    (pow_pos (inv_pos.mpr (sub_pos.mpr hp)) _)

private theorem one_le_easyRamseyBoundValue {p : ℝ} {k ℓ : ℕ}
    (hx₀ : 0 < easyX p) (hxp : easyX p < p) (hp₁ : p < 1)
    (hk : 0 < k) (hℓ : 0 < ℓ) :
    1 ≤ easyRamseyBoundValue p k ℓ := by
  have hx₁ : easyX p ≤ 1 := le_of_lt (hxp.trans hp₁)
  have hrpow : 1 ≤ easyX p ^ (-(k : ℝ) / 2) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx₀ hx₁
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hqpos : 0 < 1 - p := sub_pos.mpr hp₁
  have hqinv : 1 ≤ (1 - p)⁻¹ :=
    (one_le_inv₀ hqpos).2 (by
      have hp0 : 0 < p := hx₀.trans hxp
      linarith)
  have hqpow : 1 ≤ ((1 - p)⁻¹) ^ ℓ := one_le_pow₀ hqinv
  have hsum : (1 : ℝ) ≤ ((k + ℓ : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ k + ℓ by omega)
  unfold easyRamseyBoundValue
  nlinarith [mul_le_mul hrpow hqpow (by norm_num : (0 : ℝ) ≤ 1)
    (le_trans (by norm_num) hrpow)]

private theorem ramseyNumber_cast_le_of_floor_bound {k ℓ : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hbound : RamseyBound k ℓ ⌊B⌋₊) :
    (ramseyNumber k ℓ : ℝ) ≤ B := by
  exact (Nat.cast_le.mpr (ramseyNumber_le hbound)).trans (Nat.floor_le hB)

private theorem sub_one_lt_nat_of_floor_le {B : ℝ} {n : ℕ}
    (h : ⌊B⌋₊ ≤ n) : B - 1 < (n : ℝ) := by
  exact (Nat.sub_one_lt_floor B).trans_le (Nat.cast_le.mpr h)

private theorem cast_le_sub_one_of_lt_floor {B : ℝ} {m : ℕ}
    (hB : 0 ≤ B) (h : m < ⌊B⌋₊) : (m : ℝ) ≤ B - 1 := by
  have hsucc : m + 1 ≤ ⌊B⌋₊ := h
  have hcast : ((m + 1 : ℕ) : ℝ) ≤ (⌊B⌋₊ : ℝ) := Nat.cast_le.mpr hsucc
  have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
  push_cast at hcast
  linarith

private theorem easyRamseyBoundValue_lower {p : ℝ} {k ℓ : ℕ}
    (hx₀ : 0 < easyX p) (hxp : easyX p < p) (hp₁ : p < 1)
    (hk : 0 < k) (hℓ : 0 < ℓ) :
    4 * ((k + ℓ : ℕ) : ℝ) ≤ easyRamseyBoundValue p k ℓ := by
  have hx₁ : easyX p ≤ 1 := le_of_lt (hxp.trans hp₁)
  have hrpow : 1 ≤ easyX p ^ (-(k : ℝ) / 2) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx₀ hx₁
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hqpos : 0 < 1 - p := sub_pos.mpr hp₁
  have hp0 : 0 < p := hx₀.trans hxp
  have hqinv : 1 ≤ (1 - p)⁻¹ :=
    (one_le_inv₀ hqpos).2 (by linarith)
  have hqpow : 1 ≤ ((1 - p)⁻¹) ^ ℓ := one_le_pow₀ hqinv
  have hsnonneg : 0 ≤ 4 * (((k + ℓ : ℕ) : ℝ)) := by positivity
  unfold easyRamseyBoundValue
  calc
    4 * (((k + ℓ : ℕ) : ℝ)) =
        4 * (((k + ℓ : ℕ) : ℝ)) * 1 * 1 := by ring
    _ ≤ 4 * (((k + ℓ : ℕ) : ℝ)) *
          easyX p ^ (-(k : ℝ) / 2) * ((1 - p)⁻¹) ^ ℓ := by
      gcongr

private theorem easyRamseyBoundValue_prev {p : ℝ} {k ℓ : ℕ}
    (hp₁ : p < 1) :
    easyRamseyBoundValue p k ℓ =
      (((k + ℓ : ℕ) : ℝ) / ((k + (ℓ + 1) : ℕ) : ℝ)) * (1 - p) *
        easyRamseyBoundValue p k (ℓ + 1) := by
  have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp₁)
  have hs : ((k + (ℓ + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  unfold easyRamseyBoundValue
  push_cast
  rw [pow_succ]
  field_simp

private theorem rpow_half_square {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (x ^ (-(k : ℝ) / 2)) ^ 2 = (x⁻¹) ^ k := by
  calc
    (x ^ (-(k : ℝ) / 2)) ^ 2 =
        x ^ ((-(k : ℝ) / 2) * (2 : ℕ)) := by
          rw [Real.rpow_mul_natCast (le_of_lt hx)]
    _ = x ^ (-(k : ℝ)) := by
      congr 1
      push_cast
      ring
    _ = x⁻¹ ^ (k : ℝ) := by rw [Real.rpow_neg_eq_inv_rpow]
    _ = (x⁻¹) ^ k := by rw [Real.rpow_natCast]

private theorem easyRamseyBoundValue_sq {p : ℝ} {k ℓ : ℕ}
    (hx : 0 < easyX p) :
    easyRamseyBoundValue p k ℓ ^ 2 =
      16 * (((k + ℓ : ℕ) : ℝ)) ^ 2 * (easyX p)⁻¹ ^ k *
        ((1 - p)⁻¹) ^ (2 * ℓ) := by
  unfold easyRamseyBoundValue
  rw [mul_pow, mul_pow, mul_pow, rpow_half_square hx]
  rw [← pow_mul]
  ring

private theorem inverse_product_pow {a b q : ℝ} (h : a * b = q ^ 2)
    (n : ℕ) :
    (a⁻¹) ^ n * (b⁻¹) ^ n = (q⁻¹) ^ (2 * n) := by
  calc
    (a⁻¹) ^ n * (b⁻¹) ^ n = (a⁻¹ * b⁻¹) ^ n := by
      rw [mul_pow]
    _ = ((a * b)⁻¹) ^ n := by rw [mul_inv]
    _ = ((q ^ 2)⁻¹) ^ n := by rw [h]
    _ = ((q⁻¹) ^ 2) ^ n := by
      congr 1
      rw [inv_pow]
    _ = (q⁻¹) ^ (2 * n) := by rw [pow_mul]

private theorem easyStrongThreshold_eq {p : ℝ} {k ℓ : ℕ} :
    (((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        ((1 - easyX p)⁻¹) ^ (ℓ - 1) *
          ((p - easyX p)⁻¹) ^ (ℓ - 1)) =
      ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        ((1 - p)⁻¹) ^ (2 * (ℓ - 1)) := by
  have hpair : ((1 - easyX p)⁻¹) ^ (ℓ - 1) *
      ((p - easyX p)⁻¹) ^ (ℓ - 1) =
      ((1 - p)⁻¹) ^ (2 * (ℓ - 1)) :=
    inverse_product_pow easyX_product_identity (ℓ - 1)
  calc
    ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        ((1 - easyX p)⁻¹) ^ (ℓ - 1) *
          ((p - easyX p)⁻¹) ^ (ℓ - 1) =
      ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        (((1 - easyX p)⁻¹) ^ (ℓ - 1) *
          ((p - easyX p)⁻¹) ^ (ℓ - 1)) := by ring
    _ = _ := by rw [hpair]

private theorem easyCandidateThreshold_le_strong {p : ℝ} {k ℓ : ℕ}
    (hx₀ : 0 < easyX p) (hxp : easyX p < p) (hp₁ : p < 1)
    (hk : 0 < k) :
    easyCandidateThreshold (easyX p) p k ℓ ℓ ≤
      ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        ((1 - easyX p)⁻¹) ^ (ℓ - 1) *
          ((p - easyX p)⁻¹) ^ (ℓ - 1) := by
  have hxinv : 1 ≤ (easyX p)⁻¹ :=
    (one_le_inv₀ hx₀).2 (le_of_lt (hxp.trans hp₁))
  have hxpow : (easyX p)⁻¹ ^ (k - 1) ≤ (easyX p)⁻¹ ^ k := by
    exact pow_le_pow_right₀ hxinv (Nat.sub_le k 1)
  have hOneX : 0 < 1 - easyX p := by linarith
  have hpX : 0 < p - easyX p := sub_pos.mpr hxp
  have hnonneg :
      0 ≤ ((k + ℓ : ℕ) : ℝ) *
        ((1 - easyX p)⁻¹) ^ (ℓ - 1) *
          ((p - easyX p)⁻¹) ^ (ℓ - 1) := by positivity
  unfold easyCandidateThreshold
  nlinarith [mul_le_mul_of_nonneg_left hxpow hnonneg]

private theorem easyBound_sq_scaled_eq_strong {p : ℝ} {k ℓ : ℕ}
    (hx : 0 < easyX p) (hp : p < 1) (hk : 0 < k) (hℓ : 0 < ℓ) :
    (1 - p) ^ 2 * easyRamseyBoundValue p k ℓ ^ 2 /
        (16 * ((k + ℓ : ℕ) : ℝ)) =
      ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        ((1 - p)⁻¹) ^ (2 * (ℓ - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ.ne'
  have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hs : ((k + (m + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [easyRamseyBoundValue_sq hx]
  norm_num [Nat.succ_eq_add_one]
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
  field_simp

private theorem strongThreshold_le_cutScale {p : ℝ} {k ℓ : ℕ} {n : ℝ}
    (hx₀ : 0 < easyX p) (hxp : easyX p < p) (hp₁ : p < 1)
    (hk : 0 < k) (hℓ : 0 < ℓ)
    (hn : easyRamseyBoundValue p k ℓ - 1 < n) :
    ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
        ((1 - p)⁻¹) ^ (2 * (ℓ - 1)) ≤
      (1 - p) ^ 2 * n ^ 2 / (4 * ((k + ℓ : ℕ) : ℝ)) := by
  let B := easyRamseyBoundValue p k ℓ
  have hB_lower := easyRamseyBoundValue_lower hx₀ hxp hp₁ hk hℓ
  have hsNat : 1 ≤ k + ℓ := by omega
  have hs : (1 : ℝ) ≤ ((k + ℓ : ℕ) : ℝ) := by exact_mod_cast hsNat
  have hBtwo : 2 ≤ B := by
    dsimp [B]
    nlinarith
  have hBhalf : B / 2 ≤ B - 1 := by linarith
  have hhalf_lt : B / 2 < n := lt_of_le_of_lt hBhalf hn
  have hBnonneg : 0 ≤ B / 2 := by linarith
  have hnnonneg : 0 ≤ n := le_trans hBnonneg (le_of_lt hhalf_lt)
  have hsq : (B / 2) ^ 2 ≤ n ^ 2 :=
    (sq_le_sq₀ hBnonneg hnnonneg).2 hhalf_lt.le
  have hqnonneg : 0 ≤ (1 - p) ^ 2 := sq_nonneg _
  have hdenpos : 0 < 4 * ((k + ℓ : ℕ) : ℝ) := by positivity
  have hscaled :
      (1 - p) ^ 2 * B ^ 2 / (16 * ((k + ℓ : ℕ) : ℝ)) ≤
        (1 - p) ^ 2 * n ^ 2 / (4 * ((k + ℓ : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hsq hqnonneg
    calc
      (1 - p) ^ 2 * B ^ 2 / (16 * ((k + ℓ : ℕ) : ℝ)) =
          ((1 - p) ^ 2 * (B / 2) ^ 2) /
            (4 * ((k + ℓ : ℕ) : ℝ)) := by ring
      _ ≤ ((1 - p) ^ 2 * n ^ 2) /
            (4 * ((k + ℓ : ℕ) : ℝ)) := by
        exact div_le_div_of_nonneg_right this hdenpos.le
  rw [← easyBound_sq_scaled_eq_strong hx₀ hp₁ hk hℓ]
  exact hscaled

private theorem one_third_lt_of_easyHypothesis {p : ℝ}
    (hp : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p) :
    (1 : ℝ) / 3 < p := by
  have hspos : 0 < Real.sqrt 5 + 1 := by positivity
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsTwo : 2 < Real.sqrt 5 := by nlinarith
  have hthird : (1 : ℝ) / 3 < (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) hspos]
    nlinarith
  exact hthird.trans hp

private theorem sum_lt_p_mul_of_floor_lower {p : ℝ} {k ℓ : ℕ} {n : ℝ}
    (hpLower : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p)
    (hx₀ : 0 < easyX p) (hxp : easyX p < p) (hp₁ : p < 1)
    (hk : 0 < k) (hℓ : 0 < ℓ)
    (hn : easyRamseyBoundValue p k ℓ - 1 < n) :
    ((k + ℓ : ℕ) : ℝ) < p * n := by
  let s : ℝ := ((k + ℓ : ℕ) : ℝ)
  have hs : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ k + ℓ by omega)
  have hB := easyRamseyBoundValue_lower hx₀ hxp hp₁ hk hℓ
  have hn4 : 4 * s - 1 < n := by
    dsimp [s] at hB ⊢
    linarith
  have hnpos : 0 < n := by nlinarith
  have hpThird := one_third_lt_of_easyHypothesis hpLower
  have hmul : (1 / 3 : ℝ) * n < p * n :=
    mul_lt_mul_of_pos_right hpThird hnpos
  have hs_le : s ≤ (1 / 3 : ℝ) * (4 * s - 1) := by nlinarith
  have hscaled : (1 / 3 : ℝ) * (4 * s - 1) < (1 / 3 : ℝ) * n :=
    mul_lt_mul_of_pos_left hn4 (by norm_num)
  exact lt_of_le_of_lt hs_le (hscaled.trans hmul)

private theorem ramseyBound_easy_aux {p : ℝ}
    (hpLower : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p)
    (hp₁ : p < 1) :
    ∀ ℓ : ℕ, 0 < ℓ → ∀ k N : ℕ, 0 < k →
      ⌊easyRamseyBoundValue p k ℓ⌋₊ ≤ N → RamseyBound k ℓ N := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
      intro hℓ k N hk hN
      obtain ⟨hx₀, hxp, _⟩ := easyX_parameters hpLower hp₁
      have hBOne := one_le_easyRamseyBoundValue hx₀ hxp hp₁ hk hℓ
      have hNpos : 0 < N := by
        have hfloor : 1 ≤ ⌊easyRamseyBoundValue p k ℓ⌋₊ := by
          rw [Nat.le_floor_iff' one_ne_zero]
          simpa only [Nat.cast_one] using hBOne
        omega
      by_cases hkOne : k = 1
      · subst k
        exact (ramseyBound_one_left ℓ).mono hNpos
      by_cases hℓOne : ℓ = 1
      · subst ℓ
        exact (ramseyBound_one_right k).mono hNpos
      have hkTwo : 2 ≤ k := by omega
      have hℓTwo : 2 ≤ ℓ := by omega
      have hprevPos : 0 < ℓ - 1 := by omega
      classical
      intro G
      let B := easyRamseyBoundValue p k ℓ
      let C := easyRamseyBoundValue p k (ℓ - 1)
      let n : ℝ := N
      let s : ℝ := ((k + ℓ : ℕ) : ℝ)
      have hBpos : 0 < B := by
        dsimp [B]
        exact easyRamseyBoundValue_pos hx₀ hp₁ (by omega)
      have hCpos : 0 < C := by
        dsimp [C]
        exact easyRamseyBoundValue_pos hx₀ hp₁ (by omega)
      have hBlt : B - 1 < n := by
        dsimp [B, n]
        exact sub_one_lt_nat_of_floor_le hN
      by_cases hlargeBlue :
          ∃ v : Fin N, ⌊C⌋₊ ≤ Gᶜ.degree v
      · obtain ⟨v, hv⟩ := hlargeBlue
        have hcard : ⌊easyRamseyBoundValue p k (ℓ - 1)⌋₊ ≤
            #(Gᶜ.neighborFinset v) := by
          simpa [C, SimpleGraph.card_neighborFinset_eq_degree] using hv
        have hprevBound : RamseyBound k (ℓ - 1) #(Gᶜ.neighborFinset v) :=
          ih (ℓ - 1) (by omega) hprevPos k _ hk hcard
        rcases hprevBound.on_finset G (Gᶜ.neighborFinset v) rfl with
          hred | hblue
        · exact Or.inl (hasRedClique_mono (Finset.subset_univ _) hred)
        · right
          apply hasBlueClique_mono (Finset.subset_univ (insert v (Gᶜ.neighborFinset v)))
          simpa [Nat.sub_add_cancel hℓ] using
            hasBlueClique_insert_of_subset_neighborFinset hblue Finset.Subset.rfl
      · have hblueSmall : ∀ v : Fin N, Gᶜ.degree v < ⌊C⌋₊ := by
          simpa only [not_exists, not_le] using hlargeBlue
        have hCnonneg : 0 ≤ C := le_of_lt hCpos
        have hblueCast (v : Fin N) : (Gᶜ.degree v : ℝ) ≤ C - 1 := by
          exact cast_le_sub_one_of_lt_floor hCnonneg (hblueSmall v)
        let a : ℝ := (((k + (ℓ - 1) : ℕ) : ℝ) / s)
        have hspos : 0 < s := by
          dsimp [s]
          positivity
        have hsne : s ≠ 0 := ne_of_gt hspos
        have hnumpos : 0 < (((k + (ℓ - 1) : ℕ) : ℝ)) := by positivity
        have hapos : 0 < a := div_pos hnumpos hspos
        have hnumlt : (((k + (ℓ - 1) : ℕ) : ℝ)) < s := by
          dsimp [s]
          exact_mod_cast (show k + (ℓ - 1) < k + ℓ by omega)
        have haOne : a < 1 := (div_lt_one hspos).2 hnumlt
        have hp0 : 0 < p := hx₀.trans hxp
        have hqpos : 0 < 1 - p := sub_pos.mpr hp₁
        have hqOne : 1 - p < 1 := by linarith
        have haqOne : a * (1 - p) < 1 :=
          mul_lt_one_of_nonneg_of_lt_one_right haOne.le hqpos.le hqOne
        have hCeq : C = a * (1 - p) * B := by
          dsimp [C, a, s, B]
          simpa [Nat.sub_add_cancel hℓ] using
            (easyRamseyBoundValue_prev (p := p) (k := k) (ℓ := ℓ - 1) hp₁)
        have hfactorPos : 0 < a * (1 - p) := mul_pos hapos hqpos
        have hClt : C < a * (1 - p) * (n + 1) := by
          rw [hCeq]
          exact mul_lt_mul_of_pos_left (by linarith : B < n + 1) hfactorPos
        have hcoeff : p + (1 - p) / s = 1 - a * (1 - p) := by
          dsimp [a, s]
          have hcastEq :
              (((k + (ℓ - 1) : ℕ) : ℝ)) = ((k + ℓ : ℕ) : ℝ) - 1 := by
            push_cast
            rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]
            ring
          rw [hcastEq]
          field_simp
          ring
        let D : ℝ := (p + (1 - p) / s) * n - 1
        have hDlt : D < n - C := by
          dsimp [D]
          rw [hcoeff]
          nlinarith
        have hredCast (v : Fin N) : n - C ≤ (G.degree v : ℝ) := by
          have hdegreeNat : G.degree v + Gᶜ.degree v = N - 1 := by
            have hd := G.degree_lt_card_verts v
            simp only [Fintype.card_fin] at hd
            rw [G.degree_compl]
            simp only [Fintype.card_fin]
            omega
          have hdegreeReal :
              (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) = n - 1 := by
            dsimp [n]
            calc
              (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) =
                  ((G.degree v + Gᶜ.degree v : ℕ) : ℝ) := by push_cast; ring
              _ = ((N - 1 : ℕ) : ℝ) := by rw [hdegreeNat]
              _ = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
          linarith [hblueCast v]
        have hDdegree (v : Fin N) : D ≤ (G.degree v : ℝ) :=
          le_trans (le_of_lt hDlt) (hredCast v)
        have hsumDegree : n * D ≤ ∑ v : Fin N, (G.degree v : ℝ) := by
          calc
            n * D = ∑ _v : Fin N, D := by
              dsimp [n]
              simp
            _ ≤ ∑ v : Fin N, (G.degree v : ℝ) := by
              apply Finset.sum_le_sum
              intro v hv
              exact hDdegree v
        obtain ⟨X, Y, hXY, _hunion, hcut⟩ := exists_bipartition_excess_ge G p
        have hcutFromD :
            (n * D - p * n * (n - 1)) / 4 ≤ excess G p X Y := by
          have hleft :
              (n * D - p * n * (n - 1)) / 4 ≤
                ((∑ v : Fin N, (G.degree v : ℝ)) -
                  p * n * (n - 1)) / 4 := by
            gcongr
          exact hleft.trans (by simpa [n] using hcut)
        have hcutAlgebra :
            (n * D - p * n * (n - 1)) / 4 =
              (1 - p) * n / 4 * (n / s - 1) := by
          dsimp [D]
          field_simp [hsne]
          ring
        have hs_lt_pn : s < p * n := by
          dsimp [s, n, B] at hBlt ⊢
          exact sum_lt_p_mul_of_floor_lower hpLower hx₀ hxp hp₁ hk hℓ hBlt
        have hnpos : 0 < n := by dsimp [n]; positivity
        have hscale :
            (1 - p) ^ 2 * n ^ 2 / (4 * s) ≤
              (1 - p) * n / 4 * (n / s - 1) := by
          have hdiff :
              (1 - p) * n / 4 * (n / s - 1) -
                  (1 - p) ^ 2 * n ^ 2 / (4 * s) =
                ((1 - p) * n / (4 * s)) * (p * n - s) := by
            field_simp [hsne]
            ring
          rw [← sub_nonneg, hdiff]
          exact mul_nonneg (by positivity) (sub_nonneg.mpr hs_lt_pn.le)
        have hstrong :
            ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
                ((1 - p)⁻¹) ^ (2 * (ℓ - 1)) ≤ excess G p X Y := by
          apply (strongThreshold_le_cutScale hx₀ hxp hp₁ hk hℓ hBlt).trans
          apply hscale.trans
          rw [← hcutAlgebra]
          exact hcutFromD
        have hstrongOriginal :
            ((k + ℓ : ℕ) : ℝ) * (easyX p)⁻¹ ^ k *
                ((1 - easyX p)⁻¹) ^ (ℓ - 1) *
                  ((p - easyX p)⁻¹) ^ (ℓ - 1) ≤ excess G p X Y := by
          rw [easyStrongThreshold_eq]
          exact hstrong
        have hthreshold :
            easyCandidateThreshold (easyX p) p k ℓ ℓ ≤ excess G p X Y :=
          (easyCandidateThreshold_le_strong hx₀ hxp hp₁ hk).trans hstrongOriginal
        have hthresholdPos :
            0 < easyCandidateThreshold (easyX p) p k ℓ ℓ := by
          unfold easyCandidateThreshold
          have hOneX : 0 < 1 - easyX p := by linarith
          have hpX : 0 < p - easyX p := sub_pos.mpr hxp
          exact mul_pos
            (mul_pos
              (mul_pos (by positivity) (pow_pos (inv_pos.mpr hx₀) _))
              (pow_pos (inv_pos.mpr hOneX) _))
            (pow_pos (inv_pos.mpr hpX) _)
        have hcandidate : Candidate G X Y :=
          Candidate.of_disjoint_of_excess_pos hXY
            (lt_of_lt_of_le hthresholdPos hthreshold)
        have hgood := hcandidate.isGood_of_excess_ge hx₀ hxp hp₁ hk hℓ hℓ hthreshold
        exact hgood.to_univ

/-- Paper Theorem `t:easy`: the golden-ratio density bound, stated in a
floor-stable Ramsey-bound form. -/
theorem ramseyBound_easy
    {p : ℝ}
    (hpLower : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p)
    (hp₁ : p < 1) {k ℓ N : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (hN : ⌊easyRamseyBoundValue p k ℓ⌋₊ ≤ N) :
    RamseyBound k ℓ N :=
  ramseyBound_easy_aux hpLower hp₁ ℓ hℓ k N hk hN

private noncomputable def optimizedP (k ℓ : ℕ) : ℝ :=
  ((Real.sqrt 5 + 1) * (k : ℝ) + (2 * Real.sqrt 5 - 2) * (ℓ : ℝ)) /
    ((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ)))

private theorem easyX_optimizedP {k ℓ : ℕ} (hk : 0 < k) :
    easyX (optimizedP k ℓ) = (k : ℝ) / ((k : ℝ) + 2 * (ℓ : ℝ)) := by
  have hs : Real.sqrt 5 + 1 ≠ 0 := by positivity
  have hkℓ : (k : ℝ) + 2 * (ℓ : ℝ) ≠ 0 := by positivity
  unfold easyX optimizedP
  field_simp
  ring_nf

private theorem one_sub_optimizedP {k ℓ : ℕ} (hk : 0 < k) :
    1 - optimizedP k ℓ =
      4 * (ℓ : ℝ) /
        ((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ))) := by
  have hs : Real.sqrt 5 + 1 ≠ 0 := by positivity
  have hkℓ : (k : ℝ) + 2 * (ℓ : ℝ) ≠ 0 := by positivity
  unfold optimizedP
  field_simp
  ring

private theorem optimizedP_bounds {k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < optimizedP k ℓ ∧
      optimizedP k ℓ < 1 := by
  have hspos : 0 < Real.sqrt 5 + 1 := by positivity
  have hkℓpos : 0 < (k : ℝ) + 2 * (ℓ : ℝ) := by positivity
  have hden :
      0 < (Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ)) :=
    mul_pos hspos hkℓpos
  constructor
  · unfold optimizedP
    rw [div_lt_div_iff₀ hspos hden]
    have hid :
        (((Real.sqrt 5 + 1) * (k : ℝ) +
              (2 * Real.sqrt 5 - 2) * (ℓ : ℝ)) *
            (Real.sqrt 5 + 1)) -
          ((Real.sqrt 5 - 1) *
            ((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ)))) =
          2 * (k : ℝ) * (Real.sqrt 5 + 1) := by
      ring
    nlinarith [mul_pos (by positivity : (0 : ℝ) < 2 * k) hspos]
  · rw [optimizedP, div_lt_one hden]
    have hid :
        (Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ)) -
          ((Real.sqrt 5 + 1) * (k : ℝ) +
            (2 * Real.sqrt 5 - 2) * (ℓ : ℝ)) =
          4 * (ℓ : ℝ) := by
      ring
    nlinarith [show (0 : ℝ) < 4 * ℓ by positivity]

private theorem optimized_value_rewrite {k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    easyRamseyBoundValue (optimizedP k ℓ) k ℓ =
      4 * ((k : ℝ) + (ℓ : ℝ)) *
        (((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ))) /
          (4 * (ℓ : ℝ))) ^ ℓ *
        (((k : ℝ) + 2 * (ℓ : ℝ)) / (k : ℝ)) ^ ((k : ℝ) / 2) := by
  rw [easyRamseyBoundValue, easyX_optimizedP hk, one_sub_optimizedP hk]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by positivity
  have hs0 : Real.sqrt 5 + 1 ≠ 0 := by positivity
  have hkℓ0 : (k : ℝ) + 2 * (ℓ : ℝ) ≠ 0 := by positivity
  have hxinv :
      ((k : ℝ) / ((k : ℝ) + 2 * (ℓ : ℝ)))⁻¹ =
        ((k : ℝ) + 2 * (ℓ : ℝ)) / (k : ℝ) := by
    field_simp
  have hpInv :
      (4 * (ℓ : ℝ) /
          ((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ))))⁻¹ =
        ((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ))) /
          (4 * (ℓ : ℝ)) := by
    field_simp
  have hkneg : -(k : ℝ) / 2 = -((k : ℝ) / 2) := by ring
  rw [hkneg, Real.rpow_neg_eq_inv_rpow, hxinv, hpInv]
  simp only [Nat.cast_add]
  ring

/-- Paper Corollary `c:easy`, with its printed real-valued bound unchanged.
The last power is `Real.rpow`; the power indexed by `ℓ` is a natural power. -/
theorem ramseyNumber_le_easy_optimized {k ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    (ramseyNumber k ℓ : ℝ) ≤
      4 * ((k : ℝ) + (ℓ : ℝ)) *
        (((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * (ℓ : ℝ))) /
          (4 * (ℓ : ℝ))) ^ ℓ *
        (((k : ℝ) + 2 * (ℓ : ℝ)) / (k : ℝ)) ^ ((k : ℝ) / 2) := by
  have hk : 0 < k := lt_of_lt_of_le hℓ hℓk
  let p := optimizedP k ℓ
  have hp := optimizedP_bounds hk hℓ
  have hxpos : 0 < easyX p := by
    rw [show p = optimizedP k ℓ by rfl, easyX_optimizedP hk]
    positivity
  have honepos : 0 < 1 - p := sub_pos.mpr hp.2
  have hB : 0 ≤ easyRamseyBoundValue p k ℓ := by
    unfold easyRamseyBoundValue
    positivity
  have hfloor : RamseyBound k ℓ ⌊easyRamseyBoundValue p k ℓ⌋₊ :=
    ramseyBound_easy hp.1 hp.2 hk hℓ le_rfl
  have hcast := ramseyNumber_cast_le_of_floor_bound hB hfloor
  rw [show p = optimizedP k ℓ by rfl, optimized_value_rewrite hk hℓ] at hcast
  exact hcast

end RamseyLean
