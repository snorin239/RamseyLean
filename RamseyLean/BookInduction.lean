import RamseyLean.AsymptoticRegion
import RamseyLean.BlueBook
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The book induction

This module formalizes the density averaging, limiting estimates,
regularization, finite recursive engine, and graph-independent schedules used
to prove paper Theorem `t:bookmain`.
-/

set_option autoImplicit false

namespace RamseyLean

open Filter Set Topology
open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

omit [Fintype V] [DecidableEq V] in
private theorem redDensity_mul_card_right
    (hX : X.Nonempty) (Z : Finset V) :
    redDensity G X Z * (#Z : ℝ) =
      (redInteredgeCount G X Z : ℝ) / (#X : ℝ) := by
  by_cases hZ : Z.Nonempty
  · have hX0 : (#X : ℝ) ≠ 0 := by exact_mod_cast hX.card_ne_zero
    have hZ0 : (#Z : ℝ) ≠ 0 := by exact_mod_cast hZ.card_ne_zero
    rw [redDensity_eq_div]
    field_simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hZ]
    simp

omit [Fintype V] [DecidableEq V] in
private theorem card_mul_redDensity_mul_card_right
    (hX : X.Nonempty) (Z : Finset V) :
    (#X : ℝ) *
        (redDensity G X Z * (#Z : ℝ)) =
      redInteredgeCount G X Z := by
  rw [redDensity_mul_card_right hX]
  have hX0 : (#X : ℝ) ≠ 0 := by exact_mod_cast hX.card_ne_zero
  field_simp

/-- Paper Lemma `l:FpAvg2`: red-neighborhood restriction preserves density
on average, weighted by the restricted right-side cardinality. -/
theorem sum_density_mul_card_redNeighborhood_ge
    (h : Candidate G X Y) :
    ∑ v ∈ X,
        redDensity G X (G.neighborFinset v ∩ Y) *
          (#(G.neighborFinset v ∩ Y) : ℝ) ≥
      (redInteredgeCount G X Y : ℝ) * redDensity G X Y := by
  let p := redDensity G X Y
  have hp : p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨redDensity_nonneg X Y, redDensity_le_one X Y⟩
  have havg := sum_excess_redNeighborhood_ge (p := p) h hp
  have hbase : excess G p X Y = 0 := by
    rw [h.excess_eq_density_sub_mul]
    simp [p]
  rw [hbase, mul_zero] at havg
  have hsum_card :
      ∑ v ∈ X, (#(G.neighborFinset v ∩ Y) : ℝ) =
        (redInteredgeCount G X Y : ℝ) := by
    exact_mod_cast
      (redInteredgeCount_eq_sum_card_neighborFinset_inter (G := G) X Y).symm
  have hexcess :
      ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y) =
        (#X : ℝ) *
          ((∑ v ∈ X,
              redDensity G X (G.neighborFinset v ∩ Y) *
                (#(G.neighborFinset v ∩ Y) : ℝ)) -
            p * (redInteredgeCount G X Y : ℝ)) := by
    calc
      ∑ v ∈ X, excess G p X (G.neighborFinset v ∩ Y) =
          ∑ v ∈ X,
            ((#X : ℝ) *
                (redDensity G X (G.neighborFinset v ∩ Y) *
                  (#(G.neighborFinset v ∩ Y) : ℝ)) -
              p * (#X : ℝ) * (#(G.neighborFinset v ∩ Y) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [excess, card_mul_redDensity_mul_card_right h.left_nonempty]
      _ = (#X : ℝ) *
          ((∑ v ∈ X,
              redDensity G X (G.neighborFinset v ∩ Y) *
                (#(G.neighborFinset v ∩ Y) : ℝ)) -
            p * (∑ v ∈ X, (#(G.neighborFinset v ∩ Y) : ℝ))) := by
            simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = (#X : ℝ) *
          ((∑ v ∈ X,
              redDensity G X (G.neighborFinset v ∩ Y) *
                (#(G.neighborFinset v ∩ Y) : ℝ)) -
            p * (redInteredgeCount G X Y : ℝ)) := by
            rw [hsum_card]
  rw [hexcess] at havg
  have hXpos : (0 : ℝ) < (#X : ℝ) := by exact_mod_cast h.left_card_pos
  dsimp [p] at havg ⊢
  nlinarith

/-! ## Crude Ramsey-number bounds used by the book schedules -/

private theorem ramseyBound_choose_aux :
    ∀ a b : ℕ, RamseyBound (a + 1) (b + 1) ((a + b).choose a) := by
  intro a
  induction a with
  | zero =>
      intro b
      simpa using ramseyBound_one_left (b + 1)
  | succ a iha =>
      intro b
      induction b with
      | zero =>
          simpa using ramseyBound_one_right (a + 1 + 1)
      | succ b ihb =>
          have hrec := (iha (b + 1)).recurrence ihb
          convert hrec using 1
          rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by omega]
          rw [Nat.choose_succ_succ']
          rw [show a + (b + 1) = a + 1 + b by omega]

/-- The standard Erdős--Szekeres binomial upper bound. -/
theorem ramseyNumber_le_choose {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    ramseyNumber k m ≤ (k + m - 2).choose (k - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hindex : k + 1 + (m + 1) - 2 = k + m := by omega
  rw [hindex]
  exact ramseyNumber_le (ramseyBound_choose_aux k m)

/-- The paper's crude growth estimate `R(k,m) ≤ k^m`. -/
theorem ramseyNumber_le_pow_first {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    ramseyNumber k m ≤ k ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  calc
    ramseyNumber (k + 1) (m + 1) ≤ (k + m).choose k := by
      have hindex : k + 1 + (m + 1) - 2 = k + m := by omega
      simpa [hindex] using
        (ramseyNumber_le_choose (k := k + 1) (m := m + 1) (by omega) (by omega))
    _ = (k + m).choose m := Nat.choose_symm_add
    _ ≤ (k + 1) ^ m := Nat.choose_add_le_add_one_pow k m
    _ ≤ (k + 1) ^ (m + 1) := by
      exact Nat.pow_le_pow_right (by omega) (by omega)

namespace Candidate.IsGood

omit [Fintype V] [DecidableRel G.Adj] in
/-- A point of `asymptoticRegion0` supplies a uniform right-side Ramsey
threshold for the book induction. -/
theorem exists_right_threshold_of_mem_asymptoticRegion0
    {a b : ℝ} {t : ℕ} (hab : (a, b) ∈ asymptoticRegion0) :
    ∃ N : ℕ, ∀ {k ℓ : ℕ}, 0 < k → 0 < ℓ → N ≤ k + ℓ →
      (a⁻¹) ^ k * (b⁻¹) ^ ℓ ≤ (#Y : ℝ) →
      Candidate.IsGood G X Y k ℓ t := by
  rcases hab with ⟨ha, hb, N, hN⟩
  refine ⟨N, ?_⟩
  intro k' ℓ' hk hℓ hlarge hY
  have hramseyReal : (ramseyNumber k' ℓ' : ℝ) ≤ (#Y : ℝ) :=
    (hN k' ℓ' hk hℓ hlarge).trans hY
  have hramseyNat : ramseyNumber k' ℓ' ≤ #Y := by
    exact_mod_cast hramseyReal
  exact of_ramseyNumber_le_card_right hramseyNat

end Candidate.IsGood

section FiniteBookInterfaces

variable {v : V}

/-! ## High-blue vertices -/

@[simp]
theorem mem_highBlueVertices_iff {μ : ℝ} :
    v ∈ highBlueVertices G X μ ↔
      v ∈ X ∧ μ * (#X : ℝ) ≤ (#(Gᶜ.neighborFinset v ∩ X) : ℝ) := by
  classical
  simp [highBlueVertices]

theorem highBlueVertices_subset (μ : ℝ) :
    highBlueVertices G X μ ⊆ X := by
  intro w hw
  exact (mem_highBlueVertices_iff.mp hw).1

theorem blueDegree_lt_of_mem_sdiff_highBlueVertices {μ : ℝ}
    (hv : v ∈ X \ highBlueVertices G X μ) :
    (#(Gᶜ.neighborFinset v ∩ X) : ℝ) < μ * (#X : ℝ) := by
  have hv' := (Finset.mem_sdiff.mp hv).2
  exact lt_of_not_ge fun h => hv' (mem_highBlueVertices_iff.mpr
    ⟨(Finset.mem_sdiff.mp hv).1, h⟩)

/-! ## Exceptional-set removal and weighted selection -/

private theorem density_mul_card_redNeighborhood_le_card
    (w : V) :
    redDensity G X (G.neighborFinset w ∩ Y) *
        (#(G.neighborFinset w ∩ Y) : ℝ) ≤ (#Y : ℝ) := by
  have hd := redDensity_le_one (G := G) X (G.neighborFinset w ∩ Y)
  have hcardNat : #(G.neighborFinset w ∩ Y) ≤ #Y :=
    Finset.card_le_card Finset.inter_subset_right
  have hcard : (#(G.neighborFinset w ∩ Y) : ℝ) ≤ (#Y : ℝ) := by
    exact_mod_cast hcardNat
  calc
    redDensity G X (G.neighborFinset w ∩ Y) *
        (#(G.neighborFinset w ∩ Y) : ℝ) ≤
        1 * (#(G.neighborFinset w ∩ Y) : ℝ) := by
      gcongr
    _ ≤ (#Y : ℝ) := by simpa using hcard

/-- The total contribution of an exceptional set is at most its cardinality
times the size of the candidate's right side. -/
theorem sum_density_mul_card_redNeighborhood_le_card_mul
    (W : Finset V) :
    ∑ w ∈ W,
        redDensity G X (G.neighborFinset w ∩ Y) *
          (#(G.neighborFinset w ∩ Y) : ℝ) ≤
      (#W : ℝ) * (#Y : ℝ) := by
  calc
    ∑ w ∈ W,
        redDensity G X (G.neighborFinset w ∩ Y) *
          (#(G.neighborFinset w ∩ Y) : ℝ) ≤
        ∑ _w ∈ W, (#Y : ℝ) := by
      exact Finset.sum_le_sum fun w _hw => density_mul_card_redNeighborhood_le_card w
    _ = (#W : ℝ) * (#Y : ℝ) := by simp

omit [Fintype V] [DecidableEq V] in
private theorem exists_ge_of_weighted_sum_ge
    {U : Finset V} {f weight : V → ℝ} {q E : ℝ}
    (hw : ∀ w ∈ U, 0 ≤ weight w)
    (hq : 0 < q) (hE : 0 < E)
    (hweight : ∑ w ∈ U, weight w ≤ E)
    (hsum : q * E ≤ ∑ w ∈ U, f w * weight w) :
    ∃ w ∈ U, q ≤ f w := by
  have hU : U.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst U
    simp at hsum
    nlinarith
  obtain ⟨w, hwU, hwmax⟩ := Finset.exists_max_image U f hU
  refine ⟨w, hwU, ?_⟩
  have hsumMax :
      ∑ z ∈ U, f z * weight z ≤ f w * ∑ z ∈ U, weight z := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun z hz =>
      mul_le_mul_of_nonneg_right (hwmax z hz) (hw z hz)
  by_contra hqf
  have hflt : f w < q := lt_of_not_ge hqf
  by_cases hfw : 0 ≤ f w
  · have hprod : f w * (∑ z ∈ U, weight z) ≤ f w * E := by
      exact mul_le_mul_of_nonneg_left hweight hfw
    have : f w * E < q * E := mul_lt_mul_of_pos_right hflt hE
    linarith
  · have hweightsNonneg : 0 ≤ ∑ z ∈ U, weight z :=
      Finset.sum_nonneg fun z hz => hw z hz
    have hsumNonpos : ∑ z ∈ U, f z * weight z ≤ 0 :=
      hsumMax.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hfw) hweightsNonneg)
    nlinarith

/-- Removing a controlled exceptional subset from `l:FpAvg2` leaves a vertex
whose red-neighborhood restriction loses at most `c` in density. -/
theorem exists_mem_sdiff_density_redNeighborhood_ge
    (h : Candidate G X Y) {W : Finset V} (hWX : W ⊆ X)
    {c : ℝ} (hc : 0 ≤ c) (hcd : c < redDensity G X Y)
    (hexception :
      ∑ w ∈ W,
          redDensity G X (G.neighborFinset w ∩ Y) *
            (#(G.neighborFinset w ∩ Y) : ℝ) ≤
        c * (redInteredgeCount G X Y : ℝ)) :
    ∃ v ∈ X \ W,
      redDensity G X (G.neighborFinset v ∩ Y) ≥ redDensity G X Y - c := by
  let d := redDensity G X Y
  let E := (redInteredgeCount G X Y : ℝ)
  let weight : V → ℝ := fun w => (#(G.neighborFinset w ∩ Y) : ℝ)
  let f : V → ℝ := fun w => redDensity G X (G.neighborFinset w ∩ Y)
  have hd : 0 < d := lt_of_le_of_lt hc hcd
  have hE : 0 < E := by
    dsimp [E]
    rw [← h.redDensity_mul_card]
    have hXpos : (0 : ℝ) < #X := by exact_mod_cast h.left_card_pos
    have hYpos : (0 : ℝ) < #Y := by exact_mod_cast h.right_card_pos
    exact mul_pos (by simpa [d] using hd) (mul_pos hXpos hYpos)
  have htotal := sum_density_mul_card_redNeighborhood_ge (G := G) h
  have hsplitF :
      (∑ w ∈ W, f w * weight w) +
          ∑ w ∈ X \ W, f w * weight w =
        ∑ w ∈ X, f w * weight w := by
    simpa [add_comm] using
      (Finset.sum_sdiff hWX (f := fun w => f w * weight w))
  have hout : (d - c) * E ≤ ∑ w ∈ X \ W, f w * weight w := by
    dsimp [f, weight, d, E] at hsplitF hexception htotal ⊢
    nlinarith
  have hweightTotal :
      ∑ w ∈ X, weight w = E := by
    dsimp [weight, E]
    exact_mod_cast
      (redInteredgeCount_eq_sum_card_neighborFinset_inter (G := G) X Y).symm
  have hweight : ∑ w ∈ X \ W, weight w ≤ E := by
    have hnonneg : 0 ≤ ∑ w ∈ W, weight w := by
      exact Finset.sum_nonneg fun w _hw => by
        dsimp [weight]
        positivity
    have hsplit := Finset.sum_sdiff hWX (f := weight)
    rw [hweightTotal] at hsplit
    linarith
  have hselect := exists_ge_of_weighted_sum_ge
    (U := X \ W) (f := f) (weight := weight) (q := d - c) (E := E)
    (fun w _hw => by dsimp [weight]; positivity) (sub_pos.mpr hcd) hE hweight hout
  simpa [f, d] using hselect

/-! ## The red/blue/singleton partition and paper inequality `(e:moment2)` -/

private def redPart (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (X : Finset V) : Finset V := G.neighborFinset v ∩ X

private def bluePart (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (X : Finset V) : Finset V := Gᶜ.neighborFinset v ∩ X

private theorem redPart_union_bluePart_union_singleton
    (hv : v ∈ X) : redPart G v X ∪ bluePart G v X ∪ {v} = X := by
  ext w
  simp only [redPart, bluePart, Finset.mem_union, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  rw [SimpleGraph.compl_adj]
  constructor
  · intro h
    rcases h with (⟨_hadj, hwX⟩ | ⟨_hblue, hwX⟩) | rfl
    · exact hwX
    · exact hwX
    · exact hv
  · intro hwX
    by_cases hwv : w = v
    · exact Or.inr hwv
    · by_cases hadj : G.Adj v w
      · exact Or.inl (Or.inl ⟨hadj, hwX⟩)
      · exact Or.inl (Or.inr ⟨⟨Ne.symm hwv, hadj⟩, hwX⟩)

private theorem redPart_disjoint_bluePart :
    Disjoint (redPart G v X) (bluePart G v X) := by
  rw [Finset.disjoint_left]
  intro w hwR hwB
  have hR : G.Adj v w :=
    (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hwR).1
  have hB : Gᶜ.Adj v w :=
    (Gᶜ.mem_neighborFinset v w).mp (Finset.mem_inter.mp hwB).1
  exact ((G.compl_adj v w).mp hB).2 hR

private theorem redBluePart_union_disjoint_singleton :
    Disjoint (redPart G v X ∪ bluePart G v X) {v} := by
  rw [Finset.disjoint_left]
  intro w hw hws
  have hwv : w = v := Finset.mem_singleton.mp hws
  subst w
  rcases Finset.mem_union.mp hw with hwR | hwB
  · exact G.irrefl ((G.mem_neighborFinset v v).mp (Finset.mem_inter.mp hwR).1)
  · exact Gᶜ.irrefl ((Gᶜ.mem_neighborFinset v v).mp (Finset.mem_inter.mp hwB).1)

omit [Fintype V] [DecidableEq V] in
private theorem density_sub_mul_card_eq_excess
    (p : ℝ) (A B : Finset V) :
    (redDensity G A B - p) * (#A : ℝ) * (#B : ℝ) = excess G p A B := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · rw [excess_eq_density_sub_mul (G := G) (p := p) hA hB]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
      simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

private theorem redInteredgeCount_singleton_redNeighborhood
    (Y : Finset V) :
    redInteredgeCount G {v} (G.neighborFinset v ∩ Y) =
      #(G.neighborFinset v ∩ Y) := by
  rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
  simp

/-- Unnormalized form of paper inequality `(e:moment2)`. -/
theorem redBluePartition_moment2_unnormalized
    {p' : ℝ} (hp' : 0 ≤ p') (hv : v ∈ X) :
    let XR := G.neighborFinset v ∩ X
    let XB := Gᶜ.neighborFinset v ∩ X
    let Y' := G.neighborFinset v ∩ Y
    ((redDensity G XR Y' - p') * (#XR : ℝ) +
        (redDensity G XB Y' - p') * (#XB : ℝ) + 1) * (#Y' : ℝ) ≥
      (redDensity G X Y' - p') * (#X : ℝ) * (#Y' : ℝ) := by
  dsimp
  let XR := redPart G v X
  let XB := bluePart G v X
  let Y' := G.neighborFinset v ∩ Y
  have hpart : XR ∪ XB ∪ {v} = X := redPart_union_bluePart_union_singleton hv
  have hdisjRB : Disjoint XR XB := redPart_disjoint_bluePart
  have hdisjV : Disjoint (XR ∪ XB) {v} := redBluePart_union_disjoint_singleton
  have hexsplit1 := excess_union_left (G := G) (p := p') hdisjRB Y'
  have hexsplit2 := excess_union_left (G := G) (p := p') hdisjV Y'
  rw [hpart, hexsplit1] at hexsplit2
  have hsingleCount : redInteredgeCount G {v} Y' = #Y' := by
    exact redInteredgeCount_singleton_redNeighborhood Y
  have hsingle : excess G p' {v} Y' = (1 - p') * (#Y' : ℝ) := by
    rw [excess, hsingleCount]
    simp
    ring
  rw [hsingle] at hexsplit2
  have hXR := density_sub_mul_card_eq_excess (G := G) p' XR Y'
  have hXB := density_sub_mul_card_eq_excess (G := G) p' XB Y'
  have hX := density_sub_mul_card_eq_excess (G := G) p' X Y'
  calc
    ((redDensity G XR Y' - p') * (#XR : ℝ) +
          (redDensity G XB Y' - p') * (#XB : ℝ) + 1) * (#Y' : ℝ) =
        excess G p' XR Y' + excess G p' XB Y' + (#Y' : ℝ) := by
      rw [← hXR, ← hXB]
      ring
    _ ≥ excess G p' X Y' := by
      rw [hexsplit2]
      nlinarith [mul_nonneg hp' (Nat.cast_nonneg #Y')]
    _ = (redDensity G X Y' - p') * (#X : ℝ) * (#Y' : ℝ) := hX.symm

/-- Normalized paper inequality `(e:moment2)`. -/
theorem redBluePartition_moment2
    {p' : ℝ} (hp' : 0 ≤ p') (hv : v ∈ X)
    (hY : (G.neighborFinset v ∩ Y).Nonempty)
    (hα : 0 < redDensity G X (G.neighborFinset v ∩ Y) - p') :
    let XR := G.neighborFinset v ∩ X
    let XB := Gᶜ.neighborFinset v ∩ X
    let Y' := G.neighborFinset v ∩ Y
    let α := redDensity G X Y' - p'
    let αR := redDensity G XR Y' - p'
    let αB := redDensity G XB Y' - p'
    αR / α * ((#XR : ℝ) / (#X : ℝ)) +
        αB / α * ((#XB : ℝ) / (#X : ℝ)) +
          1 / (α * (#X : ℝ)) ≥ 1 := by
  dsimp
  have hraw := redBluePartition_moment2_unnormalized
    (G := G) (X := X) (Y := Y) (v := v) hp' hv
  have hX : X.Nonempty := ⟨v, hv⟩
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hYpos : (0 : ℝ) < #(G.neighborFinset v ∩ Y) := by
    exact_mod_cast hY.card_pos
  have hinner :
      (redDensity G (G.neighborFinset v ∩ X) (G.neighborFinset v ∩ Y) - p') *
          (#(G.neighborFinset v ∩ X) : ℝ) +
        (redDensity G (Gᶜ.neighborFinset v ∩ X) (G.neighborFinset v ∩ Y) - p') *
          (#(Gᶜ.neighborFinset v ∩ X) : ℝ) + 1 ≥
        (redDensity G X (G.neighborFinset v ∩ Y) - p') * (#X : ℝ) := by
    apply le_of_mul_le_mul_right _ hYpos
    simpa [mul_assoc] using hraw
  let α := redDensity G X (G.neighborFinset v ∩ Y) - p'
  have hden : 0 < α * (#X : ℝ) := mul_pos hα hXpos
  have hrearrange :
      (redDensity G (G.neighborFinset v ∩ X) (G.neighborFinset v ∩ Y) - p') /
            α * ((#(G.neighborFinset v ∩ X) : ℝ) / (#X : ℝ)) +
          (redDensity G (Gᶜ.neighborFinset v ∩ X) (G.neighborFinset v ∩ Y) - p') /
            α * ((#(Gᶜ.neighborFinset v ∩ X) : ℝ) / (#X : ℝ)) +
          1 / (α * (#X : ℝ)) =
        ((redDensity G (G.neighborFinset v ∩ X) (G.neighborFinset v ∩ Y) - p') *
              (#(G.neighborFinset v ∩ X) : ℝ) +
            (redDensity G (Gᶜ.neighborFinset v ∩ X) (G.neighborFinset v ∩ Y) - p') *
              (#(Gᶜ.neighborFinset v ∩ X) : ℝ) + 1) /
          (α * (#X : ℝ)) := by
    field_simp [hα.ne', hXpos.ne']
  change _ / α * _ + _ / α * _ + _ ≥ _
  rw [hrearrange]
  exact (le_div_iff₀ hden).2 (by simpa [α] using hinner)

end FiniteBookInterfaces

/-- The paper's parameter in Lemma `l:limit`. The first and last powers are
real powers, while the middle power is a natural power. -/
noncomputable def bookParameter (p μ : ℝ) (r : ℕ) : ℝ :=
  (p ^ ((r : ℝ)⁻¹) - μ) ^ r * (1 - μ) ^ (1 - (r : ℝ))

private theorem bookParameter_eq_normalized {p μ : ℝ} (hμ : μ < 1) (r : ℕ) :
    bookParameter p μ r =
      (1 - μ) * (1 + (p ^ ((r : ℝ)⁻¹) - 1) / (1 - μ)) ^ r := by
  have hd : 1 - μ ≠ 0 := (sub_pos.mpr hμ).ne'
  rw [bookParameter, Real.rpow_sub_natCast hd, Real.rpow_one]
  have hbase :
      1 + (p ^ ((r : ℝ)⁻¹) - 1) / (1 - μ) =
        (p ^ ((r : ℝ)⁻¹) - μ) / (1 - μ) := by
    field_simp
    ring
  rw [hbase, div_pow]
  field_simp

private theorem tendsto_inv_nat_nhdsGT_zero :
    Tendsto (fun r : ℕ => ((r : ℝ)⁻¹)) atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hr' : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  exact inv_pos.mpr hr'

/-- Generalized form of paper Lemma `l:limit`. The printed ordering `μ < p`
is unnecessary: positivity of `p` and the upper bound `μ < 1` suffice. -/
theorem tendsto_bookParameter {p μ : ℝ} (hp : 0 < p) (hμ : μ < 1) :
    Tendsto (bookParameter p μ) atTop
      (𝓝 (p ^ (1 / (1 - μ)) * (1 - μ))) := by
  have hp_first_order :
      Tendsto (fun r : ℕ => (r : ℝ) * (p ^ ((r : ℝ)⁻¹) - 1)) atTop
        (𝓝 (Real.log p)) := by
    have h := (tendsto_rpow_sub_one_log hp).comp tendsto_inv_nat_nhdsGT_zero
    convert h using 1
    · funext r
      simp
  have hg :
      Tendsto
        (fun r : ℕ => (r : ℝ) * ((p ^ ((r : ℝ)⁻¹) - 1) / (1 - μ)))
        atTop (𝓝 (Real.log p / (1 - μ))) := by
    simpa only [mul_div_assoc] using hp_first_order.div_const (1 - μ)
  have hpow := Real.tendsto_one_add_pow_exp_of_tendsto hg
  have hnormalized :
      Tendsto
        (fun r : ℕ =>
          (1 - μ) * (1 + (p ^ ((r : ℝ)⁻¹) - 1) / (1 - μ)) ^ r)
        atTop (𝓝 ((1 - μ) * p ^ (1 / (1 - μ)))) := by
    convert tendsto_const_nhds.mul hpow using 1
    rw [Real.rpow_def_of_pos hp]
    congr 2
    ring_nf
  simpa only [mul_comm] using hnormalized.congr' (Filter.Eventually.of_forall fun r =>
    (bookParameter_eq_normalized hμ r).symm)

/-- Use-oriented consequence of `l:limit`. The selected exponent is natural
and at least two. This remains valid without the paper's assumption `μ < p`,
which is why formal `t:bookmain` can omit that assumption. -/
theorem exists_bookExponent {p μ x₀ : ℝ}
    (hp : 0 < p) (_hp₁ : p < 1) (_hμ : 0 < μ) (hμ₁ : μ < 1)
    (hx₀ : x₀ < p ^ (1 / (1 - μ)) * (1 - μ)) :
    ∃ r : ℕ, 2 ≤ r ∧ μ < p ^ ((r : ℝ)⁻¹) ∧ x₀ < bookParameter p μ r := by
  have hp_root : Tendsto (fun r : ℕ => p ^ ((r : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun r : ℕ => ((r : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_nhds_zero_nat
    have hroot := (Real.continuousAt_const_rpow hp.ne').tendsto.comp hinv
    convert hroot using 1 <;> simp [Function.comp_def]
  have hevent_root : ∀ᶠ r : ℕ in atTop, μ < p ^ ((r : ℝ)⁻¹) :=
    hp_root.eventually (Ioi_mem_nhds hμ₁)
  have hevent_moment : ∀ᶠ r : ℕ in atTop, x₀ < bookParameter p μ r :=
    (tendsto_bookParameter hp hμ₁).eventually (Ioi_mem_nhds hx₀)
  exact ((eventually_ge_atTop (2 : ℕ)).and (hevent_root.and hevent_moment)).exists

/-! ## The capped power profile used in the final local dichotomy -/

noncomputable def bookProfile (x μ s z : ℝ) : ℝ :=
  x ^ (1 - s) * (1 - z) ^ s + μ ^ (1 - s) * z ^ s

set_option maxHeartbeats 800000 in
/-- Below its critical point, the two-term power profile is monotone. This is
the calculus input behind paper lines 409--416. -/
theorem bookProfile_monotoneOn {x μ s β : ℝ}
    (hx : 0 < x) (hμ : 0 < μ) (hs0 : 0 < s) (hs1 : s < 1)
    (hβ1 : β < 1)
    (hcap : β ≤ μ / (x + μ)) :
    MonotoneOn (bookProfile x μ s) (Icc 0 β) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) β)
  · apply Continuous.continuousOn
    unfold bookProfile
    exact (continuous_const.mul
      ((Real.continuous_rpow_const hs0.le).comp
        (continuous_const.sub continuous_id))).add
      (continuous_const.mul (Real.continuous_rpow_const hs0.le))
  · intro z hz
    rw [interior_Icc] at hz
    have hz0 : 0 < z := hz.1
    have hz1 : z < 1 := hz.2.trans hβ1
    have hid : DifferentiableAt ℝ (fun y : ℝ => y) z := differentiableAt_id
    apply DifferentiableAt.differentiableWithinAt
    unfold bookProfile
    exact ((((hid.const_sub 1).rpow_const
        (Or.inl (sub_ne_zero.mpr hz1.ne'))).const_mul (x ^ (1 - s))).add
      ((hid.rpow_const (Or.inl hz0.ne')).const_mul (μ ^ (1 - s))))
  · intro z hz
    rw [interior_Icc] at hz
    have hz0 : 0 < z := hz.1
    have hzβ : z < β := hz.2
    have hz1 : z < 1 := hzβ.trans hβ1
    have hsum : 0 < x + μ := add_pos hx hμ
    have hratio : x / (1 - z) ≤ μ / z := by
      rw [div_le_div_iff₀ (sub_pos.mpr hz1) hz0]
      have h := hzβ.le.trans hcap
      rw [le_div_iff₀ hsum] at h
      nlinarith
    have hpow :
        (x / (1 - z)) ^ (1 - s) ≤ (μ / z) ^ (1 - s) := by
      exact Real.rpow_le_rpow (by positivity) hratio (by linarith)
    have hsub : HasDerivAt (fun z : ℝ => 1 - z) (-1) z :=
      (hasDerivAt_id z).const_sub 1
    have hsubpow := hsub.rpow_const (p := s)
      (Or.inl (sub_ne_zero.mpr hz1.ne'))
    have hidpow := (hasDerivAt_id z).rpow_const (p := s) (Or.inl hz0.ne')
    have hleft := hsubpow.const_mul (x ^ (1 - s))
    have hright := hidpow.const_mul (μ ^ (1 - s))
    have hderiv := hleft.add hright
    change 0 ≤ deriv
      (fun z : ℝ => x ^ (1 - s) * (1 - z) ^ s + μ ^ (1 - s) * z ^ s) z
    have hd : deriv
        (fun z : ℝ => x ^ (1 - s) * (1 - z) ^ s + μ ^ (1 - s) * z ^ s) z =
        x ^ (1 - s) * (-1 * s * (1 - z) ^ (s - 1)) +
          μ ^ (1 - s) * (1 * s * z ^ (s - 1)) := by
      exact hderiv.deriv
    rw [hd]
    rw [Real.div_rpow (le_of_lt hx) (le_of_lt (sub_pos.mpr hz1)),
      Real.div_rpow (le_of_lt hμ) (le_of_lt hz0)] at hpow
    have hpow' :
        x ^ (1 - s) * (1 - z) ^ (s - 1) ≤
          μ ^ (1 - s) * z ^ (s - 1) := by
      rw [show s - 1 = -(1 - s) by ring,
        Real.rpow_neg (sub_pos.mpr hz1).le,
        Real.rpow_neg hz0.le, ← div_eq_mul_inv, ← div_eq_mul_inv]
      exact hpow
    nlinarith

/-- Capped form of the power-profile estimate. It is stated directly in the
shape consumed by the red/blue child dichotomy. -/
theorem bookProfile_le {x μ s β u v : ℝ}
    (hx : 0 < x) (hμ : 0 < μ) (hs0 : 0 < s) (hs1 : s < 1)
    (hμβ : μ ≤ β) (hβ1 : β < 1) (hcap : β ≤ μ / (x + μ))
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) (hvβ : v ≤ β) :
    x ^ (1 - s) * u ^ s + μ ^ (1 - s) * v ^ s ≤
      x ^ (1 - s) * (1 - μ) ^ s + β := by
  have hβ0 : 0 < β := hμ.trans_le hμβ
  have hμ1 : μ < 1 := hμβ.trans_lt hβ1
  have hOneV : 0 ≤ 1 - v := by linarith
  have hOneβ : 0 ≤ 1 - β := by linarith
  have huOneV : u ≤ 1 - v := by linarith
  have huPow : u ^ s ≤ (1 - v) ^ s :=
    Real.rpow_le_rpow hu huOneV hs0.le
  have hprofile :=
    bookProfile_monotoneOn hx hμ hs0 hs1 hβ1 hcap
      ⟨hv, hvβ⟩ ⟨hβ0.le, le_rfl⟩ hvβ
  have hμpow : μ ^ (1 - s) ≤ β ^ (1 - s) :=
    Real.rpow_le_rpow hμ.le hμβ (by linarith)
  calc
    x ^ (1 - s) * u ^ s + μ ^ (1 - s) * v ^ s ≤
        x ^ (1 - s) * (1 - v) ^ s + μ ^ (1 - s) * v ^ s := by
      gcongr
    _ = bookProfile x μ s v := rfl
    _ ≤ bookProfile x μ s β := hprofile
    _ = x ^ (1 - s) * (1 - β) ^ s + μ ^ (1 - s) * β ^ s := rfl
    _ ≤ x ^ (1 - s) * (1 - μ) ^ s + β := by
      have hfirst : (1 - β) ^ s ≤ (1 - μ) ^ s :=
        Real.rpow_le_rpow hOneβ (by linarith) hs0.le
      have hsecond : μ ^ (1 - s) * β ^ s ≤ β := by
        calc
          μ ^ (1 - s) * β ^ s ≤ β ^ (1 - s) * β ^ s := by gcongr
          _ = β ^ ((1 - s) + s) := (Real.rpow_add hβ0 _ _).symm
          _ = β := by ring_nf; exact Real.rpow_one β
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity)) hsecond

/-! ## Graph-independent slack and logarithmic schedules -/

/-- Strict slack data sufficient for the book induction. The cutoff field is
the exact inequality used by the capped power profile; it is weaker than the
paper's auxiliary cutoff and leaves the final theorem unchanged. -/
structure BookSlack (μ₀ x₀ y₀ p : ℝ) where
  r : ℕ
  ε : ℝ
  two_le_r : 2 ≤ r
  ε_pos : 0 < ε
  scale_mu : (1 + ε) * (μ₀ + ε) < 1
  sum_lt_one : μ₀ + x₀ + 2 * ε < 1
  region : (x₀ + 3 * ε, y₀ + 3 * ε) ∈ asymptoticRegionInterior
  root_gap : μ₀ + 3 * ε < (p - ε) ^ ((r : ℝ)⁻¹)
  blue_cutoff : μ₀ + 2 * ε < (μ₀ + ε) / (μ₀ + x₀ + 2 * ε)
  two_epsilon_lt : 2 * ε < p
  final_slack :
    x₀ + ε <
      ((p - ε) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * ε) ^ r *
        (1 - μ₀ - ε) ^ (1 - (r : ℝ))

private theorem limiting_value_lt_one_sub
    {μ₀ x₀ p : ℝ} (_hμ₀ : 0 < μ₀) (hμ₀1 : μ₀ < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hx : x₀ < p ^ (1 / (1 - μ₀)) * (1 - μ₀)) :
    μ₀ + x₀ < 1 := by
  have hexp : 0 < 1 / (1 - μ₀) := by positivity
  have hpow : p ^ (1 / (1 - μ₀)) < 1 :=
    Real.rpow_lt_one hp.le hp1 hexp
  have hsub : 0 < 1 - μ₀ := sub_pos.mpr hμ₀1
  have hmul : p ^ (1 / (1 - μ₀)) * (1 - μ₀) < 1 - μ₀ := by
    simpa using mul_lt_of_lt_one_left hsub hpow
  linarith

/-- The strict hypotheses of `t:bookmain` select all analytic slack at once. -/
theorem exists_bookSlack
    {μ₀ x₀ y₀ p : ℝ}
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (_hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hxstrict : x₀ < p ^ (1 / (1 - μ₀)) * (1 - μ₀))
    (hregion : (x₀, y₀) ∈ asymptoticRegionInterior) :
    Nonempty (BookSlack μ₀ x₀ y₀ p) := by
  obtain ⟨r, hr2, hroot, hparam⟩ :=
    exists_bookExponent hp.1 hp.2 hμ₀.1 hμ₀.2 hxstrict
  have hsum : μ₀ + x₀ < 1 :=
    limiting_value_lt_one_sub hμ₀.1 hμ₀.2 hp.1 hp.2 hxstrict
  have hcutoff : μ₀ < μ₀ / (μ₀ + x₀) := by
    have hden : 0 < μ₀ + x₀ := add_pos hμ₀.1 hx₀.1
    rw [lt_div_iff₀ hden]
    exact mul_lt_of_lt_one_right hμ₀.1 hsum

  let root : ℝ → ℝ := fun e ↦ (p - e) ^ ((r : ℝ)⁻¹)
  let shifted : ℝ → ℝ := fun e ↦
    (root e - μ₀ - 3 * e) ^ r *
      (1 - μ₀ - e) ^ (1 - (r : ℝ))
  have hroot_cont : ContinuousAt root 0 := by
    dsimp [root]
    exact (continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (by simpa using hp.1.ne'))
  have hlast_cont :
      ContinuousAt (fun e : ℝ ↦ (1 - μ₀ - e) ^ (1 - (r : ℝ))) 0 := by
    exact ((continuousAt_const.sub continuousAt_const).sub continuousAt_id).rpow_const
      (Or.inl (by simpa using (sub_pos.mpr hμ₀.2).ne'))
  have hshifted_cont : ContinuousAt shifted 0 := by
    dsimp [shifted]
    exact ((hroot_cont.sub continuousAt_const).sub
      (continuousAt_const.mul continuousAt_id)).pow r |>.mul hlast_cont

  have hscale_ev : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) * (μ₀ + e) < 1 := by
    exact ((continuousAt_const.add continuousAt_id).mul
      (continuousAt_const.add continuousAt_id)).eventually
        (Iio_mem_nhds (by simpa using hμ₀.2))
  have hsum_ev : ∀ᶠ e : ℝ in 𝓝 0, μ₀ + x₀ + 2 * e < 1 := by
    exact ((continuousAt_const.add continuousAt_const).add
      (continuousAt_const.mul continuousAt_id)).eventually
        (Iio_mem_nhds (by simpa using hsum))
  have hregion_ev : ∀ᶠ e : ℝ in 𝓝 0,
      (x₀ + 3 * e, y₀ + 3 * e) ∈ asymptoticRegionInterior := by
    have hg : ContinuousAt (fun e : ℝ ↦ (x₀ + 3 * e, y₀ + 3 * e)) 0 :=
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).prodMk
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
    exact hg.eventually_mem (isOpen_interior.mem_nhds
      (by simpa [asymptoticRegionInterior] using hregion))
  have hroot_ev : ∀ᶠ e : ℝ in 𝓝 0, μ₀ + 3 * e < root e := by
    exact (continuousAt_const.add
      (continuousAt_const.mul continuousAt_id)).eventually_lt hroot_cont
        (by simpa [root] using hroot)
  have hcutoff_ev : ∀ᶠ e : ℝ in 𝓝 0,
      μ₀ + 2 * e < (μ₀ + e) / (μ₀ + x₀ + 2 * e) := by
    have hleft : ContinuousAt (fun e : ℝ ↦ μ₀ + 2 * e) 0 :=
      continuousAt_const.add (continuousAt_const.mul continuousAt_id)
    have hright : ContinuousAt
        (fun e : ℝ ↦ (μ₀ + e) / (μ₀ + x₀ + 2 * e)) 0 := by
      exact (continuousAt_const.add continuousAt_id).div
        ((continuousAt_const.add continuousAt_const).add
          (continuousAt_const.mul continuousAt_id))
        (by simpa using (add_pos hμ₀.1 hx₀.1).ne')
    exact hleft.eventually_lt hright (by simpa using hcutoff)
  have hp_ev : ∀ᶠ e : ℝ in 𝓝 0, 2 * e < p := by
    exact (continuousAt_const.mul continuousAt_id).eventually
      (Iio_mem_nhds (by simpa using hp.1))
  have hfinal_ev : ∀ᶠ e : ℝ in 𝓝 0, x₀ + e < shifted e := by
    have hleft : ContinuousAt (fun e : ℝ ↦ x₀ + e) 0 :=
      continuousAt_const.add continuousAt_id
    apply hleft.eventually_lt hshifted_cont
    simpa [shifted, root, bookParameter] using hparam

  have hall : ∀ᶠ e : ℝ in 𝓝 0,
      (1 + e) * (μ₀ + e) < 1 ∧
      μ₀ + x₀ + 2 * e < 1 ∧
      (x₀ + 3 * e, y₀ + 3 * e) ∈ asymptoticRegionInterior ∧
      μ₀ + 3 * e < root e ∧
      μ₀ + 2 * e < (μ₀ + e) / (μ₀ + x₀ + 2 * e) ∧
      2 * e < p ∧ x₀ + e < shifted e :=
    hscale_ev.and (hsum_ev.and (hregion_ev.and (hroot_ev.and
      (hcutoff_ev.and (hp_ev.and hfinal_ev)))))
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  rcases (mem_closure_iff_nhds.mp hzero) _ hall with ⟨ε, hε, hεpos⟩
  exact ⟨{
    r := r
    ε := ε
    two_le_r := hr2
    ε_pos := hεpos
    scale_mu := hε.1
    sum_lt_one := hε.2.1
    region := hε.2.2.1
    root_gap := hε.2.2.2.1
    blue_cutoff := hε.2.2.2.2.1
    two_epsilon_lt := hε.2.2.2.2.2.1
    final_slack := hε.2.2.2.2.2.2
  }⟩

namespace BookSlack

theorem epsilon_mem_Ioo {μ₀ x₀ y₀ p : ℝ} (s : BookSlack μ₀ x₀ y₀ p)
    (_hμ₀ : 0 < μ₀) (hx₀ : 0 < x₀) : s.ε ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨s.ε_pos, ?_⟩
  linarith [s.sum_lt_one]

/-- The high-blue threshold gains a factor `1+ε` over the moment's `μ`. -/
theorem blue_gain_ratio {μ₀ x₀ y₀ p : ℝ} (s : BookSlack μ₀ x₀ y₀ p)
    (hx₀ : 0 < x₀) :
    (1 + s.ε) * (μ₀ + s.ε) ≤ μ₀ + 2 * s.ε := by
  have hunit : μ₀ + s.ε ≤ 1 := by
    linarith [s.sum_lt_one, s.ε_pos]
  have hmul : s.ε * (μ₀ + s.ε) ≤ s.ε := by
    exact mul_le_of_le_one_right s.ε_pos.le hunit
  nlinarith

/-- Each original unit-square coordinate gains a factor `1+ε` after shifting. -/
theorem base_scale {z : ℝ} (hz : z ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    z ≤ (z + ε) / (1 + ε) := by
  rw [le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hz hε.le
  nlinarith

end BookSlack

/-- The paper's logarithmic blue-book spine size, with `n = k+t`. -/
noncomputable def bookSpineSize (ε : ℝ) (r n : ℕ) : ℕ :=
  ⌈(2 * (r : ℝ) * Real.log (n : ℝ) - (r : ℝ) * Real.log ε + Real.log 2) /
      Real.log (1 + ε)⌉₊

/-- The quadratic page-clique size used by the blue-book lemma. -/
noncomputable def bookPageSize (μ : ℝ) (b : ℕ) : ℕ :=
  ⌈10 * μ⁻¹ * (b : ℝ) ^ 2⌉₊

theorem bookSpineSize_pos {ε : ℝ} {r n : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) (hn : 0 < n) :
    0 < bookSpineSize ε r n := by
  rw [bookSpineSize, Nat.ceil_pos]
  have hlogε : Real.log ε < 0 := Real.log_neg hε.1 hε.2
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogbase : 0 < Real.log (1 + ε) :=
    Real.log_pos (by linarith [hε.1])
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hneg : 0 < -(r : ℝ) * Real.log ε := by
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr (by exact_mod_cast hr)) hlogε
  have hfirst : 0 ≤ 2 * (r : ℝ) * Real.log (n : ℝ) := by positivity
  exact div_pos (by linarith) hlogbase

private theorem exp_book_gain_identity {ε : ℝ} {r n : ℕ}
    (hε : 0 < ε) (hn : 0 < n) :
    Real.exp
        (2 * (r : ℝ) * Real.log (n : ℝ) -
          (r : ℝ) * Real.log ε + Real.log 2) =
      2 * ((((n : ℝ) ^ 2) / ε) ^ r) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show 2 * (r : ℝ) * Real.log (n : ℝ) -
        (r : ℝ) * Real.log ε + Real.log 2 =
      Real.log 2 + (r : ℝ) * (Real.log ((n : ℝ) ^ 2) - Real.log ε) by
        rw [Real.log_pow]; ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_nat_mul, Real.exp_sub, Real.exp_log (sq_pos_of_pos hnR),
    Real.exp_log hε]

/-- The logarithmic schedule has exactly the gain needed in the big-blue step. -/
theorem bookSpineSize_gain {ε : ℝ} {r n : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hn : 0 < n) :
    2 * ((((n : ℝ) ^ 2) / ε) ^ r) ≤
      (1 + ε) ^ (bookSpineSize ε r n) := by
  let A := 2 * (r : ℝ) * Real.log (n : ℝ) -
    (r : ℝ) * Real.log ε + Real.log 2
  let L := Real.log (1 + ε)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith [hε.1])
  have hceil : A / L ≤ (bookSpineSize ε r n : ℝ) := by
    simpa [bookSpineSize, A, L] using
      (Nat.le_ceil (A / L) : A / L ≤ (⌈A / L⌉₊ : ℝ))
  have hA : A ≤ L * (bookSpineSize ε r n : ℝ) := by
    have h := (div_le_iff₀ hL).mp hceil
    simpa [mul_comm] using h
  calc
    2 * ((((n : ℝ) ^ 2) / ε) ^ r) = Real.exp A := by
      symm
      exact exp_book_gain_identity hε.1 hn
    _ ≤ Real.exp (L * (bookSpineSize ε r n : ℝ)) := Real.exp_le_exp.mpr hA
    _ = (1 + ε) ^ (bookSpineSize ε r n) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by linarith [hε.1])]

/-- The quadratic page schedule satisfies the scale hypothesis of `l:BBook`. -/
theorem bookPageSize_scale {μ : ℝ} {b : ℕ} (hμ : 0 < μ) :
    10 * (b : ℝ) ^ 2 ≤ μ * (bookPageSize μ b : ℝ) := by
  have hceil : 10 * μ⁻¹ * (b : ℝ) ^ 2 ≤ (bookPageSize μ b : ℝ) := by
    simpa [bookPageSize] using
      (Nat.le_ceil (10 * μ⁻¹ * (b : ℝ) ^ 2) :
        10 * μ⁻¹ * (b : ℝ) ^ 2 ≤
          (⌈10 * μ⁻¹ * (b : ℝ) ^ 2⌉₊ : ℝ))
  calc
    10 * (b : ℝ) ^ 2 = μ * (10 * μ⁻¹ * (b : ℝ) ^ 2) := by
      field_simp
    _ ≤ μ * (bookPageSize μ b : ℝ) := mul_le_mul_of_nonneg_left hceil hμ.le

/-- The spine schedule is bounded by a constant times `log n + 1`. -/
theorem exists_bookSpineSize_log_bound {ε : ℝ} {r : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (bookSpineSize ε r n : ℝ) ≤ C * (Real.log (n : ℝ) + 1) := by
  let L := Real.log (1 + ε)
  let c₁ := 2 * (r : ℝ) / L
  let c₂ := (-(r : ℝ) * Real.log ε + Real.log 2) / L
  let C := c₁ + c₂ + 1
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith [hε.1])
  have hlogε : Real.log ε < 0 := Real.log_neg hε.1 hε.2
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 < c₂ := by
    dsimp [c₂]
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hterm : 0 ≤ -(r : ℝ) * Real.log ε := by
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg r)) hlogε.le
    exact div_pos (by linarith) hL
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  let A := 2 * (r : ℝ) * Real.log (n : ℝ) -
    (r : ℝ) * Real.log ε + Real.log 2
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hfirst : 0 ≤ 2 * (r : ℝ) * Real.log (n : ℝ) := by positivity
    have hterm : 0 ≤ -(r : ℝ) * Real.log ε := by
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg r)) hlogε.le
    linarith
  have hz : 0 ≤ A / L := div_nonneg hA hL.le
  have hceil : (bookSpineSize ε r n : ℝ) < A / L + 1 := by
    simpa [bookSpineSize, A, L] using Nat.ceil_lt_add_one hz
  have hsplit : A / L + 1 = c₁ * Real.log (n : ℝ) + c₂ + 1 := by
    dsimp [A, c₁, c₂]
    field_simp
    ring
  calc
    (bookSpineSize ε r n : ℝ) ≤ A / L + 1 := hceil.le
    _ = c₁ * Real.log (n : ℝ) + c₂ + 1 := hsplit
    _ ≤ C * (Real.log (n : ℝ) + 1) := by
      dsimp [C]
      nlinarith [mul_nonneg hc₂.le hlogn]

/-- Consequently the page schedule is bounded by `C (log n + 1)^2`. -/
theorem exists_bookPageSize_log_sq_bound {ε μ : ℝ} {r : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (bookPageSize μ (bookSpineSize ε r n) : ℝ) ≤
        C * (Real.log (n : ℝ) + 1) ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := exists_bookSpineSize_log_bound (r := r) hε
  let C := 10 * μ⁻¹ * B ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  let q := Real.log (n : ℝ) + 1
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hb : (bookSpineSize ε r n : ℝ) ≤ B * q := by
    simpa [q] using hbound n hn
  have hb0 : (0 : ℝ) ≤ bookSpineSize ε r n := by positivity
  have hBq0 : 0 ≤ B * q := mul_nonneg hB.le (zero_le_one.trans hq)
  have hsq : (bookSpineSize ε r n : ℝ) ^ 2 ≤ (B * q) ^ 2 :=
    pow_le_pow_left₀ hb0 hb 2
  have hz : 0 ≤ 10 * μ⁻¹ * (bookSpineSize ε r n : ℝ) ^ 2 := by positivity
  have hceil :
      (bookPageSize μ (bookSpineSize ε r n) : ℝ) ≤
        10 * μ⁻¹ * (bookSpineSize ε r n : ℝ) ^ 2 + 1 := by
    exact (Nat.ceil_lt_add_one hz).le
  calc
    (bookPageSize μ (bookSpineSize ε r n) : ℝ) ≤
        10 * μ⁻¹ * (bookSpineSize ε r n : ℝ) ^ 2 + 1 := hceil
    _ ≤ 10 * μ⁻¹ * (B * q) ^ 2 + 1 := by gcongr
    _ ≤ C * q ^ 2 := by
      dsimp [C]
      have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
      rw [mul_pow]
      nlinarith

/-! ### Uniform absorption of the subexponential losses -/

/-- A little-`o` term relative to `a^n` can be absorbed uniformly by one
additive exponent shift. This is the formal mechanism behind choosing `L₀`
independently of `k+t`. -/
private theorem exists_expShift_absorbing
    {f : ℕ → ℝ} {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : f =o[atTop] fun n : ℕ ↦ a ^ n) :
    ∃ L : ℕ, ∀ n ℓ : ℕ, L ≤ ℓ → f n ≤ c * a ^ (n + ℓ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf.bound hc)
  have hsmall : ∀ᶠ ℓ : ℕ in atTop,
      ∀ n ∈ Finset.range N, f n ≤ c * a ^ (n + ℓ) := by
    rw [Finset.eventually_all]
    intro n _hn
    have hpow : Tendsto (fun ℓ : ℕ ↦ c * a ^ n * a ^ ℓ) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt ha).const_mul_atTop
        (mul_pos hc (pow_pos (zero_lt_one.trans ha) n))
    filter_upwards [hpow.eventually_gt_atTop (f n)] with ℓ hℓ
    simpa [pow_add, mul_assoc] using hℓ.le
  obtain ⟨L, hL⟩ := eventually_atTop.mp hsmall
  refine ⟨L, fun n ℓ hLℓ ↦ ?_⟩
  by_cases hn : N ≤ n
  · have hnorm := hN n hn
    have hfn : f n ≤ c * a ^ n := by
      calc
        f n ≤ ‖f n‖ := by
          rw [Real.norm_eq_abs]
          exact le_abs_self _
        _ ≤ c * ‖a ^ n‖ := hnorm
        _ = c * a ^ n := by
          rw [norm_pow, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans ha)]
    calc
      f n ≤ c * a ^ n := hfn
      _ ≤ c * a ^ (n + ℓ) := by
        rw [pow_add]
        have hbase : 0 ≤ c * a ^ n :=
          mul_nonneg hc.le (pow_nonneg (zero_lt_one.trans ha).le n)
        calc
          c * a ^ n = (c * a ^ n) * 1 := by ring
          _ ≤ (c * a ^ n) * a ^ ℓ :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ ha.le) hbase
          _ = c * (a ^ n * a ^ ℓ) := by ring
  · exact hL ℓ hLℓ n (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))

private theorem initialLoss_isLittleO {ε a : ℝ} {r : ℕ}
    (_hε : 0 < ε) (ha : 1 < a) :
    (fun n : ℕ ↦ (((n : ℝ) / ε) ^ r)) =o[atTop]
      fun n : ℕ ↦ a ^ n := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) r ha).const_mul_left
    ((ε⁻¹) ^ r)
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using h

private theorem pageSquareLoss_isLittleO {ε μ a : ℝ} {r : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ) (ha : 1 < a) :
    (fun n : ℕ ↦
      5 * (bookPageSize μ (bookSpineSize ε r n) : ℝ) ^ 2) =o[atTop]
        fun n : ℕ ↦ a ^ n := by
  obtain ⟨C, hC, hpage⟩ := exists_bookPageSize_log_sq_bound (r := r) hε hμ
  have hO :
      (fun n : ℕ ↦ 5 * (bookPageSize μ (bookSpineSize ε r n) : ℝ) ^ 2)
        =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 4) := by
    refine Asymptotics.IsBigO.of_bound (5 * C ^ 2) ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := Nat.zero_lt_of_lt hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlog : Real.log (n : ℝ) + 1 ≤ (n : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hnR]
    have hq0 : 0 ≤ Real.log (n : ℝ) + 1 := by
      have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have := Real.log_nonneg hnOne
      linarith
    have hm : (bookPageSize μ (bookSpineSize ε r n) : ℝ) ≤
        C * (n : ℝ) ^ 2 := by
      calc
        _ ≤ C * (Real.log (n : ℝ) + 1) ^ 2 := hpage n hnpos
        _ ≤ C * (n : ℝ) ^ 2 := by gcongr
    have hm0 : (0 : ℝ) ≤ bookPageSize μ (bookSpineSize ε r n) := by positivity
    have hCn0 : 0 ≤ C * (n : ℝ) ^ 2 := by positivity
    have hsq : (bookPageSize μ (bookSpineSize ε r n) : ℝ) ^ 2 ≤
        (C * (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hm0 hm 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    calc
      5 * (bookPageSize μ (bookSpineSize ε r n) : ℝ) ^ 2 ≤
          5 * (C * (n : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (5 * C ^ 2) * (n : ℝ) ^ 4 := by ring
  exact hO.trans_isLittleO (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 4 ha)

private theorem ramseyScheduleLoss_isLittleO {ε μ a : ℝ} {r : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ) (ha : 1 < a) :
    (fun n : ℕ ↦
      (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n) + 3)) =o[atTop]
        fun n : ℕ ↦ a ^ n := by
  obtain ⟨C, hC, hpage⟩ := exists_bookPageSize_log_sq_bound (r := r) hε hμ
  let d := (1 + a) / 2
  have hd1 : 1 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hd0 : 0 < d := zero_lt_one.trans hd1
  have hlogd : 0 < Real.log d := Real.log_pos hd1
  let η := Real.log d / (8 * (C + 3))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hlo :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 3) =o[atTop]
        fun n : ℕ ↦ (n : ℝ) :=
    Real.isLittleO_pow_log_id_atTop.natCast_atTop
  have hlogBound := hlo.bound hη
  have hevent : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n) + 3) ≤ d ^ n := by
    filter_upwards [hlogBound,
      eventually_ge_atTop (Nat.ceil (Real.exp 1))] with n hnlog hnlarge
    have hnexp : Real.exp 1 ≤ (n : ℝ) :=
      Nat.le_ceil (Real.exp 1) |>.trans (by exact_mod_cast hnlarge)
    have hnR : (0 : ℝ) < n := (Real.exp_pos 1).trans_le hnexp
    have hlogone : 1 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos 1) hnR hnexp
    have hlog0 : 0 ≤ Real.log (n : ℝ) := zero_le_one.trans hlogone
    have hnlog' : Real.log (n : ℝ) ^ 3 ≤ η * (n : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_pos hnR] using hnlog
    have hnpos : 0 < n := by exact_mod_cast hnR
    have hm := hpage n hnpos
    have hq0 : 0 ≤ Real.log (n : ℝ) + 1 := by linarith
    have hm3 :
        (bookPageSize μ (bookSpineSize ε r n) + 3 : ℕ) ≤
          (C + 3) * (Real.log (n : ℝ) + 1) ^ 2 := by
      exact_mod_cast show
        (bookPageSize μ (bookSpineSize ε r n) : ℝ) + 3 ≤
          (C + 3) * (Real.log (n : ℝ) + 1) ^ 2 by
            calc
              _ ≤ C * (Real.log (n : ℝ) + 1) ^ 2 + 3 := by linarith
              _ ≤ _ := by
                have hq1 : 1 ≤ (Real.log (n : ℝ) + 1) ^ 2 :=
                  one_le_pow₀ (by linarith : 1 ≤ Real.log (n : ℝ) + 1)
                nlinarith
    have hadd : Real.log (n : ℝ) + 1 ≤ 2 * Real.log (n : ℝ) := by linarith
    have hsquare : (Real.log (n : ℝ) + 1) ^ 2 ≤
        (2 * Real.log (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hq0 hadd 2
    have hlogCube :
        (C + 3) * (Real.log (n : ℝ) + 1) ^ 2 * Real.log (n : ℝ) ≤
          8 * (C + 3) * Real.log (n : ℝ) ^ 3 := by
      calc
        _ ≤ (C + 3) * (2 * Real.log (n : ℝ)) ^ 2 * Real.log (n : ℝ) := by
          gcongr
        _ ≤ 8 * (C + 3) * Real.log (n : ℝ) ^ 3 := by
          have hC3 : 0 ≤ C + 3 := by positivity
          nlinarith [mul_nonneg hC3 (pow_nonneg hlog0 3)]
    have hexponent :
        (bookPageSize μ (bookSpineSize ε r n) + 3 : ℕ) *
            Real.log (n : ℝ) ≤
          (n : ℝ) * Real.log d := by
      have hmul := mul_le_mul_of_nonneg_right hm3 hlog0
      calc
        _ ≤ (C + 3) * (Real.log (n : ℝ) + 1) ^ 2 *
            Real.log (n : ℝ) := hmul
        _ ≤ 8 * (C + 3) * Real.log (n : ℝ) ^ 3 := hlogCube
        _ ≤ (n : ℝ) * Real.log d := by
          have hden : 0 < 8 * (C + 3) := by positivity
          calc
            8 * (C + 3) * Real.log (n : ℝ) ^ 3 ≤
                8 * (C + 3) * (η * (n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hnlog' hden.le
            _ = (n : ℝ) * Real.log d := by
              dsimp [η]
              field_simp [hden.ne']
    calc
      (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n) + 3) =
          Real.exp ((bookPageSize μ (bookSpineSize ε r n) + 3 : ℕ) *
            Real.log (n : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log hnR]
      _ ≤ Real.exp ((n : ℝ) * Real.log d) := Real.exp_le_exp.mpr hexponent
      _ = d ^ n := by rw [Real.exp_nat_mul, Real.exp_log hd0]
  have hO :
      (fun n : ℕ ↦
        (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n) + 3)) =O[atTop]
          fun n : ℕ ↦ d ^ n := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hevent] with n hn
    rw [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity :
        0 ≤ (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n) + 3)),
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hd0.le n)]
    exact hn
  exact hO.trans_isLittleO (isLittleO_pow_pow_of_lt_left hd0.le hda)

/-- The graph-independent asymptotic size estimates needed after the slack is
fixed. The exceptional-set field is stated after clearing the `n^3`
denominator. -/
structure BookAsymptoticScaleBounds (ε μ p : ℝ) (r L : ℕ) : Prop where
  spine_pos : ∀ n : ℕ, 0 < n → 0 < bookSpineSize ε r n
  page_pos : ∀ n : ℕ, 0 < n →
    0 < bookPageSize μ (bookSpineSize ε r n)
  page_scale : ∀ n : ℕ,
    10 * (bookSpineSize ε r n : ℝ) ^ 2 ≤
      μ * (bookPageSize μ (bookSpineSize ε r n) : ℝ)
  blue_gain : ∀ n : ℕ, 0 < n →
    2 * ((((n : ℝ) ^ 2) / ε) ^ r) ≤
      (1 + ε) ^ (bookSpineSize ε r n)
  initial_loss : ∀ n ℓ : ℕ, 0 < n → L ≤ ℓ →
    (((n : ℝ) / ε) ^ r) ≤ (1 + ε) ^ (n + ℓ)
  five_page_sq : ∀ n ℓ : ℕ, 0 < n → L ≤ ℓ →
    5 * (bookPageSize μ (bookSpineSize ε r n) : ℝ) ^ 2 ≤
      (1 + ε) ^ (n + ℓ)
  exceptional_ramsey : ∀ n ℓ : ℕ, 0 < n → L ≤ ℓ →
    (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n) + 3) ≤
      ε * (p - ε) * (1 + ε) ^ (n + ℓ)
  alpha_error : ∀ n ℓ : ℕ, 0 < n → L ≤ ℓ →
    (n : ℝ) ^ 2 ≤ ε ^ 2 * (1 + ε) ^ (n + ℓ)

/-- A single graph-independent `L₀` realizes every scale inequality in the
book induction, uniformly for all `n = k+t`. -/
theorem exists_bookAsymptoticScaleBounds {ε μ p : ℝ} {r : ℕ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ) (hεp : ε < p) (hr : 0 < r) :
    ∃ L : ℕ, BookAsymptoticScaleBounds ε μ p r L := by
  let a := 1 + ε
  have ha : 1 < a := by dsimp [a]; linarith [hε.1]
  obtain ⟨Linit, hinit⟩ := exists_expShift_absorbing ha one_pos
    (initialLoss_isLittleO (r := r) hε.1 ha)
  obtain ⟨Lpage, hpage⟩ := exists_expShift_absorbing ha one_pos
    (pageSquareLoss_isLittleO (r := r) hε hμ ha)
  have hcoeff : 0 < ε * (p - ε) := mul_pos hε.1 (sub_pos.mpr hεp)
  obtain ⟨Lramsey, hramsey⟩ := exists_expShift_absorbing ha hcoeff
    (ramseyScheduleLoss_isLittleO (r := r) hε hμ ha)
  obtain ⟨Lalpha, halpha⟩ := exists_expShift_absorbing ha (sq_pos_of_pos hε.1)
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2 ha)
  let L := max Linit (max Lpage (max Lramsey Lalpha))
  refine ⟨L, {
    spine_pos := ?_
    page_pos := ?_
    page_scale := ?_
    blue_gain := ?_
    initial_loss := ?_
    five_page_sq := ?_
    exceptional_ramsey := ?_
    alpha_error := ?_
  }⟩
  · intro n hn
    exact bookSpineSize_pos hε hr hn
  · intro n hn
    rw [bookPageSize, Nat.ceil_pos]
    have hb := bookSpineSize_pos hε hr hn
    positivity
  · intro n
    exact bookPageSize_scale hμ
  · intro n hn
    exact bookSpineSize_gain hε hn
  · intro n ℓ hn hL
    simpa [a] using hinit n ℓ (le_trans (le_max_left _ _) hL)
  · intro n ℓ hn hL
    have hLpage : Lpage ≤ ℓ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right Linit _)) hL
    simpa [a] using hpage n ℓ hLpage
  · intro n ℓ hn hL
    have hLramsey : Lramsey ≤ ℓ := by
      apply le_trans _ hL
      exact le_trans (le_trans (le_max_left _ _) (le_max_right Lpage _))
        (le_max_right Linit _)
    simpa [a] using hramsey n ℓ hLramsey
  · intro n ℓ hn hL
    have hLalpha : Lalpha ≤ ℓ := by
      apply le_trans _ hL
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_max_right _ _)
    simpa [a] using halpha n ℓ hLalpha

namespace BookAsymptoticScaleBounds

/-- Consumer form of `initial_loss`, matching line 346 of the paper. -/
theorem initial_moment_gain {ε μ p : ℝ} {r L n ℓ : ℕ}
    (h : BookAsymptoticScaleBounds ε μ p r L) (hε : 0 < ε) (hn : 0 < n)
    (hL : L ≤ ℓ) :
    1 ≤ (ε / (n : ℝ)) ^ r * (1 + ε) ^ (n + ℓ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : (ε / (n : ℝ)) * ((n : ℝ) / ε) = 1 := by
    field_simp [hε.ne', hnR.ne']
  calc
    (1 : ℝ) = (ε / (n : ℝ)) ^ r * (((n : ℝ) / ε) ^ r) := by
      rw [← mul_pow, hprod, one_pow]
    _ ≤ (ε / (n : ℝ)) ^ r * (1 + ε) ^ (n + ℓ) := by
      gcongr
      exact h.initial_loss n ℓ hn hL

/-- Consumer form of the exceptional Ramsey loss after restoring `n^3` in
the denominator. -/
theorem exceptional_fraction {ε μ p : ℝ} {r L n ℓ : ℕ}
    (h : BookAsymptoticScaleBounds ε μ p r L) (hn : 0 < n) (hL : L ≤ ℓ) :
    (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n)) ≤
      (ε * (p - ε) / (n : ℝ) ^ 3) * (1 + ε) ^ (n + ℓ) := by
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hn3]
  simpa [pow_add, mul_assoc] using h.exceptional_ramsey n ℓ hn hL

/-- If a Ramsey term has already been bounded by `n^m`, the exact exceptional
set estimate used in line 365 follows immediately. -/
theorem exceptional_of_le_pow {ε μ p w : ℝ} {r L n ℓ : ℕ}
    (h : BookAsymptoticScaleBounds ε μ p r L) (hn : 0 < n) (hL : L ≤ ℓ)
    (hw : w ≤ (n : ℝ) ^ (bookPageSize μ (bookSpineSize ε r n))) :
    w ≤ (ε * (p - ε) / (n : ℝ) ^ 3) * (1 + ε) ^ (n + ℓ) :=
  hw.trans (h.exceptional_fraction hn hL)

/-- Consumer form of `alpha_error`, exactly the last `1/(α|X|)` estimate
once `α ≥ ε/n²` and `|X| ≥ (1+ε)^(n+ℓ)` are substituted. -/
theorem alpha_fraction {ε μ p : ℝ} {r L n ℓ : ℕ}
    (h : BookAsymptoticScaleBounds ε μ p r L) (hε : 0 < ε) (hn : 0 < n)
    (hL : L ≤ ℓ) :
    (n : ℝ) ^ 2 / (ε * (1 + ε) ^ (n + ℓ)) ≤ ε := by
  have hden : 0 < ε * (1 + ε) ^ (n + ℓ) := by positivity
  rw [div_le_iff₀ hden]
  have := h.alpha_error n ℓ hn hL
  nlinarith

end BookAsymptoticScaleBounds

private theorem normalized_bookContribution_le
    {d x α a N M : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hd : 0 < d) (hx : 0 < x) (hα : 0 < α)
    (hN : 0 < N) (hM : 0 ≤ M)
    (hfail : ¬(0 ≤ a ∧ x * α ^ r * N ≤ d * a ^ r * M)) :
    d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) ≤
      x ^ ((r : ℝ)⁻¹) * (M / N) ^ (1 - (r : ℝ)⁻¹) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hq0 : (0 : ℝ) < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  have hq1 : (r : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hrR]
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hr)
  have hs0 : (0 : ℝ) < 1 - (r : ℝ)⁻¹ := sub_pos.mpr hq1
  have hMN0 : 0 ≤ M / N := div_nonneg hM hN.le
  by_cases ha : 0 ≤ a
  · have hstrict : d * a ^ r * M < x * α ^ r * N := by
      exact lt_of_not_ge (fun h ↦ hfail ⟨ha, h⟩)
    by_cases hMzero : M = 0
    · subst M
      simp [hs0.ne']
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
      have hMNpos : 0 < M / N := div_pos hMpos hN
      have hαpow : 0 < α ^ r := pow_pos hα r
      have hden : 0 < α ^ r * N := mul_pos hαpow hN
      have hnormalized :
          d * (a / α) ^ r * (M / N) < x := by
        calc
          d * (a / α) ^ r * (M / N) =
              (d * a ^ r * M) / (α ^ r * N) := by
                rw [div_pow]
                field_simp
          _ < (x * α ^ r * N) / (α ^ r * N) :=
            div_lt_div_of_pos_right hstrict hden
          _ = x := by field_simp
      let A := d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) ^ ((r : ℝ)⁻¹)
      have hA0 : 0 ≤ A := by
        dsimp [A]
        positivity
      have hApow : A ^ r < x := by
        dsimp [A]
        rw [mul_pow, mul_pow,
          Real.rpow_inv_natCast_pow hd.le hr0.ne',
          Real.rpow_inv_natCast_pow hMN0 hr0.ne']
        exact hnormalized
      have hAroot : A ≤ x ^ ((r : ℝ)⁻¹) := by
        apply (Real.le_rpow_inv_iff_of_pos hA0 hx.le hrR).2
        rw [Real.rpow_natCast]
        exact hApow.le
      have hmul := mul_le_mul_of_nonneg_right hAroot
        (Real.rpow_nonneg hMN0 (1 - (r : ℝ)⁻¹))
      calc
        d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) =
            A * (M / N) ^ (1 - (r : ℝ)⁻¹) := by
              symm
              calc
                A * (M / N) ^ (1 - (r : ℝ)⁻¹) =
                    d ^ ((r : ℝ)⁻¹) * (a / α) *
                      ((M / N) ^ ((r : ℝ)⁻¹) *
                        (M / N) ^ (1 - (r : ℝ)⁻¹)) := by
                          dsimp [A]
                          ring
                _ = d ^ ((r : ℝ)⁻¹) * (a / α) *
                      (M / N) ^ ((r : ℝ)⁻¹ + (1 - (r : ℝ)⁻¹)) := by
                        rw [Real.rpow_add hMNpos]
                _ = d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) := by
                        rw [show (r : ℝ)⁻¹ + (1 - (r : ℝ)⁻¹) = 1 by ring,
                          Real.rpow_one]
        _ ≤ x ^ ((r : ℝ)⁻¹) *
            (M / N) ^ (1 - (r : ℝ)⁻¹) := hmul
  · have ha' : a < 0 := lt_of_not_ge ha
    have hleft : d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) ≤ 0 := by
      have hdiv : a / α ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha'.le hα.le
      have hprod : d ^ ((r : ℝ)⁻¹) * (a / α) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hd.le _) hdiv
      exact mul_nonpos_of_nonpos_of_nonneg hprod hMN0
    exact hleft.trans (by positivity)

private theorem critical_bookProfile_of_final_slack
    {μ₀ x₀ ε p : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hε : 0 < ε) (hx₀ : 0 < x₀)
    (hβ1 : μ₀ + 2 * ε < 1)
    (hrootGap : μ₀ + 3 * ε < (p - ε) ^ ((r : ℝ)⁻¹))
    (hfinal :
      x₀ + ε <
        ((p - ε) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * ε) ^ r *
          (1 - μ₀ - ε) ^ (1 - (r : ℝ))) :
    (x₀ + ε) ^ ((r : ℝ)⁻¹) *
          (1 - (μ₀ + ε)) ^ (1 - (r : ℝ)⁻¹) +
        (μ₀ + 2 * ε) + ε < (p - ε) ^ ((r : ℝ)⁻¹) := by
  let A := (p - ε) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * ε
  let B := 1 - μ₀ - ε
  have hr0 : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hq0 : (0 : ℝ) < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hx : 0 < x₀ + ε := add_pos hx₀ hε
  have hroot := Real.rpow_lt_rpow hx.le (by simpa [A, B] using hfinal) hq0
  have hroot' :
      (x₀ + ε) ^ ((r : ℝ)⁻¹) <
        A * B ^ ((r : ℝ)⁻¹ - 1) := by
    calc
      (x₀ + ε) ^ ((r : ℝ)⁻¹) <
          (A ^ r * B ^ (1 - (r : ℝ))) ^ ((r : ℝ)⁻¹) := hroot
      _ = (A ^ r) ^ ((r : ℝ)⁻¹) *
          (B ^ (1 - (r : ℝ))) ^ ((r : ℝ)⁻¹) := by
            rw [Real.mul_rpow (pow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)]
      _ = A * B ^ ((1 - (r : ℝ)) * (r : ℝ)⁻¹) := by
            rw [Real.pow_rpow_inv_natCast hA.le hr0.ne']
            rw [← Real.rpow_mul hB.le]
      _ = A * B ^ ((r : ℝ)⁻¹ - 1) := by
            congr 2
            field_simp
  have hBpow : 0 < B ^ (1 - (r : ℝ)⁻¹) := Real.rpow_pos_of_pos hB _
  have hneg : B ^ ((r : ℝ)⁻¹ - 1) =
      (B ^ (1 - (r : ℝ)⁻¹))⁻¹ := by
    rw [show (r : ℝ)⁻¹ - 1 = -(1 - (r : ℝ)⁻¹) by ring,
      Real.rpow_neg hB.le]
  rw [hneg, ← div_eq_mul_inv] at hroot'
  have hmain :
      (x₀ + ε) ^ ((r : ℝ)⁻¹) * B ^ (1 - (r : ℝ)⁻¹) < A :=
    (lt_div_iff₀ hBpow).mp hroot'
  dsimp [A, B] at hmain ⊢
  have hbaseEq : 1 - (μ₀ + ε) = 1 - μ₀ - ε := by ring
  rw [hbaseEq]
  linarith

/-- Concrete local red/blue dichotomy for the schedules used in `t:bookmain`.
The size hypothesis implies the error estimate `1 / (α * NX) ≤ ε`. -/
theorem bookLocalDichotomy
    {μ₀ x₀ ε p : ℝ} {r n minLeftSize : ℕ}
    (hr : 2 ≤ r) (hn : 4 ≤ n)
    (hε : 0 < ε) (hμ₀ : 0 < μ₀) (hx₀ : 0 < x₀)
    (hfloor : 0 < p - ε) (hp1 : p < 1)
    (hβ1 : μ₀ + 2 * ε < 1)
    (hcap : μ₀ + 2 * ε ≤
      (μ₀ + ε) / ((x₀ + ε) + (μ₀ + ε)))
    (hcritical :
      (x₀ + ε) ^ ((r : ℝ)⁻¹) *
          (1 - (μ₀ + ε)) ^ (1 - (r : ℝ)⁻¹) +
        (μ₀ + 2 * ε) + ε < (p - ε) ^ ((r : ℝ)⁻¹))
    (hsize : (n : ℝ) ^ 2 ≤ ε ^ 2 * (minLeftSize : ℝ))
    {NX NR NB α αR αB : ℝ}
    (hNX : (minLeftSize : ℝ) ≤ NX)
    (hα : ε / (n : ℝ) ^ 2 ≤ α)
    (hNR : 0 ≤ NR) (hNB : 0 ≤ NB) (hcards : NR + NB ≤ NX)
    (hblue : NB ≤ (μ₀ + 2 * ε) * NX)
    (hmoment : α * NX ≤ αR * NR + αB * NB + 1) :
    (0 ≤ αR ∧
      (x₀ + ε) * α ^ r * NX ≤ (p - ε) * αR ^ r * NR) ∨
    (0 ≤ αB ∧
      (μ₀ + ε) * α ^ r * NX ≤ (p - ε) * αB ^ r * NB) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hq0 : (0 : ℝ) < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  have hq1 : (r : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hrR]
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hr)
  have hs0 : (0 : ℝ) < 1 - (r : ℝ)⁻¹ := sub_pos.mpr hq1
  have hs1 : 1 - (r : ℝ)⁻¹ < 1 := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 4) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hminPos : (0 : ℝ) < minLeftSize := by
    have hεSq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hprod : 0 < ε ^ 2 * (minLeftSize : ℝ) := hnSq.trans_le hsize
    nlinarith
  have hNXpos : 0 < NX := hminPos.trans_le hNX
  have hαpos : 0 < α := by
    exact (div_pos hε hnSq).trans_le hα
  have hx : 0 < x₀ + ε := add_pos hx₀ hε
  have hμ : 0 < μ₀ + ε := add_pos hμ₀ hε
  have hβ : 0 < μ₀ + 2 * ε := by linarith
  have hμβ : μ₀ + ε ≤ μ₀ + 2 * ε := by linarith
  have hu : 0 ≤ NR / NX := div_nonneg hNR hNXpos.le
  have hv : 0 ≤ NB / NX := div_nonneg hNB hNXpos.le
  have huv : NR / NX + NB / NX ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hNXpos).2 hcards
  have hvβ : NB / NX ≤ μ₀ + 2 * ε := by
    exact (div_le_iff₀ hNXpos).2 (by simpa [mul_comm] using hblue)
  have hprofile :
      (x₀ + ε) ^ ((r : ℝ)⁻¹) *
          (NR / NX) ^ (1 - (r : ℝ)⁻¹) +
        (μ₀ + ε) ^ ((r : ℝ)⁻¹) *
          (NB / NX) ^ (1 - (r : ℝ)⁻¹) ≤
      (x₀ + ε) ^ ((r : ℝ)⁻¹) *
          (1 - (μ₀ + ε)) ^ (1 - (r : ℝ)⁻¹) +
        (μ₀ + 2 * ε) := by
    have h := bookProfile_le hx hμ hs0 hs1 hμβ hβ1 hcap
      hu hv huv hvβ
    simpa [show 1 - (1 - (r : ℝ)⁻¹) = (r : ℝ)⁻¹ by ring] using h
  have hsizeX : (n : ℝ) ^ 2 ≤ ε ^ 2 * NX := by
    calc
      (n : ℝ) ^ 2 ≤ ε ^ 2 * (minLeftSize : ℝ) := hsize
      _ ≤ ε ^ 2 * NX := by gcongr
  have hNXlower : (n : ℝ) ^ 2 / ε ^ 2 ≤ NX :=
    (div_le_iff₀ (sq_pos_of_pos hε)).2 (by simpa [mul_comm] using hsizeX)
  have hproduct :
      (ε / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / ε ^ 2) ≤ α * NX :=
    mul_le_mul hα hNXlower (by positivity) hαpos.le
  have hinv : ε⁻¹ ≤ α * NX := by
    calc
      ε⁻¹ = (ε / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / ε ^ 2) := by
        field_simp
      _ ≤ α * NX := hproduct
  have hone : 1 ≤ ε * (α * NX) := by
    calc
      (1 : ℝ) = ε * ε⁻¹ := by field_simp
      _ ≤ ε * (α * NX) := mul_le_mul_of_nonneg_left hinv hε.le
  have hαNX : 0 < α * NX := mul_pos hαpos hNXpos
  have herrOne : 1 / (α * NX) ≤ ε := by
    apply (div_le_iff₀ hαNX).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hone
  have hrootOne : (p - ε) ^ ((r : ℝ)⁻¹) ≤ 1 := by
    exact Real.rpow_le_one hfloor.le (by linarith) hq0.le
  have herr :
      (p - ε) ^ ((r : ℝ)⁻¹) / (α * NX) ≤ ε := by
    calc
      (p - ε) ^ ((r : ℝ)⁻¹) / (α * NX) ≤ 1 / (α * NX) :=
        div_le_div_of_nonneg_right hrootOne hαNX.le
      _ ≤ ε := herrOne
  by_contra h
  have hredFail : ¬(0 ≤ αR ∧
      (x₀ + ε) * α ^ r * NX ≤ (p - ε) * αR ^ r * NR) :=
    fun hred ↦ h (Or.inl hred)
  have hblueFail : ¬(0 ≤ αB ∧
      (μ₀ + ε) * α ^ r * NX ≤ (p - ε) * αB ^ r * NB) :=
    fun hblueAlt ↦ h (Or.inr hblueAlt)
  have hred := normalized_bookContribution_le (a := αR)
    hr hfloor hx hαpos hNXpos hNR hredFail
  have hblue' := normalized_bookContribution_le (a := αB)
    hr hfloor hμ hαpos hNXpos hNB hblueFail
  have hmomentNorm :
      1 ≤ (αR / α) * (NR / NX) + (αB / α) * (NB / NX) +
        1 / (α * NX) := by
    have hratio :
        (αR / α) * (NR / NX) + (αB / α) * (NB / NX) +
            1 / (α * NX) =
          (αR * NR + αB * NB + 1) / (α * NX) := by
      field_simp
    rw [hratio]
    apply (le_div_iff₀ hαNX).2
    simpa using hmoment
  have hroot0 : 0 ≤ (p - ε) ^ ((r : ℝ)⁻¹) :=
    Real.rpow_nonneg hfloor.le _
  have hmomentRoot := mul_le_mul_of_nonneg_left hmomentNorm hroot0
  have htotal :
      (p - ε) ^ ((r : ℝ)⁻¹) ≤
        (x₀ + ε) ^ ((r : ℝ)⁻¹) *
            (NR / NX) ^ (1 - (r : ℝ)⁻¹) +
          (μ₀ + ε) ^ ((r : ℝ)⁻¹) *
            (NB / NX) ^ (1 - (r : ℝ)⁻¹) +
          (p - ε) ^ ((r : ℝ)⁻¹) / (α * NX) := by
    calc
      (p - ε) ^ ((r : ℝ)⁻¹) =
          (p - ε) ^ ((r : ℝ)⁻¹) * 1 := by ring
      _ ≤ (p - ε) ^ ((r : ℝ)⁻¹) *
          ((αR / α) * (NR / NX) + (αB / α) * (NB / NX) +
            1 / (α * NX)) := hmomentRoot
      _ = (p - ε) ^ ((r : ℝ)⁻¹) * (αR / α) * (NR / NX) +
          (p - ε) ^ ((r : ℝ)⁻¹) * (αB / α) * (NB / NX) +
          (p - ε) ^ ((r : ℝ)⁻¹) / (α * NX) := by ring
      _ ≤ (x₀ + ε) ^ ((r : ℝ)⁻¹) *
            (NR / NX) ^ (1 - (r : ℝ)⁻¹) +
          (μ₀ + ε) ^ ((r : ℝ)⁻¹) *
            (NB / NX) ^ (1 - (r : ℝ)⁻¹) +
          (p - ε) ^ ((r : ℝ)⁻¹) / (α * NX) := by
            gcongr
  have hupper :
      (x₀ + ε) ^ ((r : ℝ)⁻¹) *
            (NR / NX) ^ (1 - (r : ℝ)⁻¹) +
          (μ₀ + ε) ^ ((r : ℝ)⁻¹) *
            (NB / NX) ^ (1 - (r : ℝ)⁻¹) +
          (p - ε) ^ ((r : ℝ)⁻¹) / (α * NX) ≤
        (x₀ + ε) ^ ((r : ℝ)⁻¹) *
            (1 - (μ₀ + ε)) ^ (1 - (r : ℝ)⁻¹) +
          (μ₀ + 2 * ε) + ε := by
    exact add_le_add hprofile herr
  exact (not_lt_of_ge (htotal.trans hupper)) hcritical

/-- The local dichotomy with hypotheses matching `BookSlack`. -/
theorem bookLocalDichotomy_of_slack
    {μ₀ x₀ ε p : ℝ} {r n minLeftSize : ℕ}
    (hr : 2 ≤ r) (hn : 4 ≤ n)
    (hε : 0 < ε) (hμ₀ : 0 < μ₀) (hx₀ : 0 < x₀) (hp1 : p < 1)
    (hsum : μ₀ + x₀ + 2 * ε < 1)
    (hcutoff : μ₀ + 2 * ε <
      (μ₀ + ε) / (μ₀ + x₀ + 2 * ε))
    (htwo : 2 * ε < p)
    (hrootGap : μ₀ + 3 * ε < (p - ε) ^ ((r : ℝ)⁻¹))
    (hfinal :
      x₀ + ε <
        ((p - ε) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * ε) ^ r *
          (1 - μ₀ - ε) ^ (1 - (r : ℝ)))
    (hsize : (n : ℝ) ^ 2 ≤ ε ^ 2 * (minLeftSize : ℝ))
    {NX NR NB α αR αB : ℝ}
    (hNX : (minLeftSize : ℝ) ≤ NX)
    (hα : ε / (n : ℝ) ^ 2 ≤ α)
    (hNR : 0 ≤ NR) (hNB : 0 ≤ NB) (hcards : NR + NB ≤ NX)
    (hblue : NB ≤ (μ₀ + 2 * ε) * NX)
    (hmoment : α * NX ≤ αR * NR + αB * NB + 1) :
    (0 ≤ αR ∧
      (x₀ + ε) * α ^ r * NX ≤ (p - ε) * αR ^ r * NR) ∨
    (0 ≤ αB ∧
      (μ₀ + ε) * α ^ r * NX ≤ (p - ε) * αB ^ r * NB) := by
  have hfloor : 0 < p - ε := by linarith
  have hβ1 : μ₀ + 2 * ε < 1 := by linarith
  have hcap : μ₀ + 2 * ε ≤
      (μ₀ + ε) / ((x₀ + ε) + (μ₀ + ε)) := by
    have hden : (x₀ + ε) + (μ₀ + ε) = μ₀ + x₀ + 2 * ε := by ring
    rw [hden]
    exact hcutoff.le
  have hcritical := critical_bookProfile_of_final_slack
    hr hε hx₀ hβ1 hrootGap hfinal
  exact bookLocalDichotomy hr hn hε hμ₀ hx₀ hfloor hp1 hβ1 hcap
    hcritical hsize hNX hα hNR hNB hcards hblue hmoment

/-- The moment potential used in the strengthened book induction. The
exponent is natural because `exists_bookExponent` selects an integer. -/
noncomputable def bookMoment (q : ℝ) (r : ℕ)
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℝ :=
  (redDensity G X Y - q) ^ r * (#X : ℝ) * (#Y : ℝ)

section Regularization

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The one-shot degree-regularized core of `X` relative to `Y`. This is a
finite implementation of the iterative deletion paragraph in `t:bookmain`. -/
noncomputable def redRegularCore (H : SimpleGraph W) [DecidableRel H.Adj]
    (q : ℝ) (A B : Finset W) : Finset W :=
  A.filter fun v ↦
    q * (#B : ℝ) ≤ (#(H.neighborFinset v ∩ B) : ℝ)

@[simp]
theorem mem_redRegularCore_iff {q : ℝ} {A B : Finset W} {v : W} :
    v ∈ redRegularCore H q A B ↔
      v ∈ A ∧ q * (#B : ℝ) ≤ (#(H.neighborFinset v ∩ B) : ℝ) := by
  classical
  simp [redRegularCore]

theorem redRegularCore_subset (q : ℝ) (A B : Finset W) :
    redRegularCore H q A B ⊆ A := by
  classical
  intro v hv
  exact (mem_redRegularCore_iff.mp hv).1

/-- Every nonempty subset of the regularized core has density at least `q`
toward the fixed right side. -/
theorem redDensity_ge_of_subset_redRegularCore
    {q : ℝ} {A B C : Finset W} (hC : C.Nonempty) (hB : B.Nonempty)
    (hCA : C ⊆ redRegularCore H q A B) :
    q ≤ redDensity H C B := by
  classical
  have hterm : ∀ v ∈ C,
      q * (#B : ℝ) ≤ (#(H.neighborFinset v ∩ B) : ℝ) := by
    intro v hv
    exact (mem_redRegularCore_iff.mp (hCA hv)).2
  have hsum :
      (#C : ℝ) * (q * (#B : ℝ)) ≤ redInteredgeCount H C B := by
    calc
      (#C : ℝ) * (q * (#B : ℝ)) =
          ∑ _v ∈ C, q * (#B : ℝ) := by simp
      _ ≤ ∑ v ∈ C, (#(H.neighborFinset v ∩ B) : ℝ) := by
        exact Finset.sum_le_sum fun v hv ↦ hterm v hv
      _ = redInteredgeCount H C B := by
        exact_mod_cast (redInteredgeCount_eq_sum_card_neighborFinset_inter
          (G := H) C B).symm
  have hdensity := redDensity_mul_card (G := H) hC hB
  have hCpos : (0 : ℝ) < #C := by exact_mod_cast hC.card_pos
  have hBpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  rw [← hdensity] at hsum
  apply le_of_mul_le_mul_right _ (mul_pos hCpos hBpos)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsum

/-- If the original pair has density at least `q`, its regularized core is
nonempty. -/
theorem redRegularCore_nonempty
    {q : ℝ} {A B : Finset W} (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : q ≤ redDensity H A B) :
    (redRegularCore H q A B).Nonempty := by
  classical
  have hdensity := redDensity_mul_card (G := H) hA hB
  have hsum :
      ∑ _v ∈ A, q * (#B : ℝ) ≤
        ∑ v ∈ A, (#(H.neighborFinset v ∩ B) : ℝ) := by
    calc
      ∑ _v ∈ A, q * (#B : ℝ) =
          q * ((#A : ℝ) * (#B : ℝ)) := by simp; ring
      _ ≤ redDensity H A B * ((#A : ℝ) * (#B : ℝ)) := by
        gcongr
      _ = redInteredgeCount H A B := hdensity
      _ = ∑ v ∈ A, (#(H.neighborFinset v ∩ B) : ℝ) := by
        exact_mod_cast redInteredgeCount_eq_sum_card_neighborFinset_inter
          (G := H) A B
  obtain ⟨v, hvA, hv⟩ := Finset.exists_le_of_sum_le hA hsum
  exact ⟨v, mem_redRegularCore_iff.mpr ⟨hvA, hv⟩⟩

/-- Removing all vertices below the fixed degree threshold cannot decrease
the `q`-excess. -/
theorem excess_le_redRegularCore {q : ℝ} {A B : Finset W} :
    excess H q A B ≤ excess H q (redRegularCore H q A B) B := by
  classical
  let C := redRegularCore H q A B
  let D := A \ C
  have hCA : C ⊆ A := redRegularCore_subset q A B
  have hCD : Disjoint C D := by
    dsimp [D]
    exact Finset.disjoint_left.mpr fun v hvC hvD ↦
      (Finset.mem_sdiff.mp hvD).2 hvC
  have hCDA : C ∪ D = A := by
    simpa [D] using Finset.union_sdiff_of_subset hCA
  have hDterm : ∀ v ∈ D,
      (#(H.neighborFinset v ∩ B) : ℝ) ≤ q * (#B : ℝ) := by
    intro v hv
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have hvC : v ∉ C := (Finset.mem_sdiff.mp hv).2
    have hnot : ¬ q * (#B : ℝ) ≤
        (#(H.neighborFinset v ∩ B) : ℝ) := by
      intro hdegree
      exact hvC (mem_redRegularCore_iff.mpr ⟨hvA, hdegree⟩)
    exact (lt_of_not_ge hnot).le
  have hDcount :
      (redInteredgeCount H D B : ℝ) ≤ q * (#D : ℝ) * (#B : ℝ) := by
    calc
      (redInteredgeCount H D B : ℝ) =
          ∑ v ∈ D, (#(H.neighborFinset v ∩ B) : ℝ) := by
        exact_mod_cast redInteredgeCount_eq_sum_card_neighborFinset_inter
          (G := H) D B
      _ ≤ ∑ _v ∈ D, q * (#B : ℝ) := by
        exact Finset.sum_le_sum fun v hv ↦ hDterm v hv
      _ = q * (#D : ℝ) * (#B : ℝ) := by simp; ring
  have hDexcess : excess H q D B ≤ 0 := by
    unfold excess
    linarith
  have hadd := excess_union_left (G := H) (p := q) hCD B
  rw [hCDA] at hadd
  linarith

end Regularization

/-- Excess-normalized form of `bookMoment`. In this form, deleting low-degree
vertices is monotone in its two factors. -/
noncomputable def bookExcessMoment (q : ℝ) (r : ℕ)
    {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (A B : Finset W) : ℝ :=
  (excess H q A B) ^ r *
    (((#A : ℝ) * (#B : ℝ))⁻¹) ^ (r - 1)

theorem bookExcessMoment_eq_bookMoment
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {q : ℝ} {r : ℕ} {A B : Finset W}
    (hA : A.Nonempty) (hB : B.Nonempty) (hr : 0 < r) :
    bookExcessMoment q r H A B = bookMoment q r H A B := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hcard : (0 : ℝ) < (#A : ℝ) * (#B : ℝ) := by
    positivity
  have hA0 : (#A : ℝ) ≠ 0 := by positivity
  have hB0 : (#B : ℝ) ≠ 0 := by positivity
  rw [bookExcessMoment, bookMoment,
    excess_eq_density_sub_mul (G := H) (p := q) hA hB]
  simp only [Nat.succ_sub_one, mul_pow, pow_succ, inv_pow]
  field_simp [hA0, hB0]

/-- One-shot degree regularization increases the normalized moment. -/
theorem bookExcessMoment_le_redRegularCore
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {q : ℝ} {r : ℕ} {A B : Finset W}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : q ≤ redDensity H A B) :
    bookExcessMoment q r H A B ≤
      bookExcessMoment q r H (redRegularCore H q A B) B := by
  classical
  let C := redRegularCore H q A B
  have hC : C.Nonempty := redRegularCore_nonempty hA hB hd
  have hCA : C ⊆ A := redRegularCore_subset q A B
  have hcardNat : #C ≤ #A := Finset.card_le_card hCA
  have hcard :
      (#C : ℝ) * (#B : ℝ) ≤ (#A : ℝ) * (#B : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardNat) (by positivity)
  have hCprod : (0 : ℝ) < (#C : ℝ) * (#B : ℝ) := by positivity
  have hAprod : (0 : ℝ) < (#A : ℝ) * (#B : ℝ) := by positivity
  have hinv :
      (((#A : ℝ) * (#B : ℝ))⁻¹) ^ (r - 1) ≤
        (((#C : ℝ) * (#B : ℝ))⁻¹) ^ (r - 1) :=
    pow_le_pow_left₀ (inv_nonneg.mpr hAprod.le)
      ((inv_le_inv₀ hAprod hCprod).2 hcard) _
  have hEA : 0 ≤ excess H q A B := by
    rw [excess_eq_density_sub_mul (G := H) (p := q) hA hB]
    positivity
  have hEC : excess H q A B ≤ excess H q C B := by
    exact excess_le_redRegularCore (H := H) (q := q) (A := A) (B := B)
  have hECnonneg : 0 ≤ excess H q C B := hEA.trans hEC
  rw [bookExcessMoment, bookExcessMoment]
  exact mul_le_mul
    (pow_le_pow_left₀ hEA hEC r) hinv
    (pow_nonneg (inv_nonneg.mpr hAprod.le) _) (pow_nonneg hECnonneg _)

/-- Combined degree-regularization interface for `t:bookmain`. It returns a
subcandidate with hereditary red density and no loss in the paper's moment. -/
theorem exists_redDegreeRegularized
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {q : ℝ} {r : ℕ} {A B : Finset W}
    (h : Candidate H A B) (hd : q ≤ redDensity H A B) (hr : 0 < r) :
    ∃ A' : Finset W,
      Candidate H A' B ∧ A' ⊆ A ∧
      (∀ ⦃C : Finset W⦄, C.Nonempty → C ⊆ A' →
        q ≤ redDensity H C B) ∧
      bookMoment q r H A B ≤ bookMoment q r H A' B := by
  classical
  let A' := redRegularCore H q A B
  have hA' : A'.Nonempty :=
    redRegularCore_nonempty h.left_nonempty h.right_nonempty hd
  have hA'A : A' ⊆ A := redRegularCore_subset q A B
  have hC : Candidate H A' B :=
    h.subcandidate hA'A Finset.Subset.rfl hA' h.right_nonempty
  refine ⟨A', hC, hA'A, ?_, ?_⟩
  · intro C hC hCA'
    exact redDensity_ge_of_subset_redRegularCore hC h.right_nonempty hCA'
  · calc
      bookMoment q r H A B = bookExcessMoment q r H A B :=
        (bookExcessMoment_eq_bookMoment h.left_nonempty h.right_nonempty hr).symm
      _ ≤ bookExcessMoment q r H A' B :=
        bookExcessMoment_le_redRegularCore h.left_nonempty h.right_nonempty hd
      _ = bookMoment q r H A' B :=
        bookExcessMoment_eq_bookMoment hA' h.right_nonempty hr

/-! ## Abstract strong-induction engine -/

section BookInductionCore

/-- The right-hand side of the strengthened moment invariant. -/
noncomputable def bookTarget (x y μ : ℝ) (ℓ k t : ℕ) : ℝ :=
  (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ t

/-- The exact invariant to which strong induction is applied. Passing the
threshold as a sequence keeps the finite induction independent of the later
choice `q n = p - ε / n`. -/
def BookAdmissible (q : ℕ → ℝ) (x y μ : ℝ) (r ℓ k t : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : Prop :=
  Candidate G X Y ∧
    q (k + t) ≤ redDensity G X Y ∧
    bookTarget x y μ ℓ k t ≤ bookMoment (q (k + t)) r G X Y

/-- One recursive step: either goodness is already known, or there is a
strictly smaller admissible child whose goodness lifts to the parent. -/
def HasBookStep (q : ℕ → ℝ) (x y μ : ℝ) (r ℓ k t : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : Prop :=
  Candidate.IsGood G X Y k ℓ t ∨
    ∃ k' t' : ℕ, ∃ X' Y' : Finset V,
      0 < k' ∧ 0 < t' ∧ k' + t' < k + t ∧
      BookAdmissible q x y μ r ℓ k' t' G X' Y' ∧
      (Candidate.IsGood G X' Y' k' ℓ t' →
        Candidate.IsGood G X Y k ℓ t)

/-- Kernel-level strong-induction engine. All graph and numerical work is
concentrated in `hstep`; the recursion itself has no asymptotic content. -/
theorem bookStrongInductionCore
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ : ℕ}
    (hstep : ∀ {k t : ℕ} {X Y : Finset V},
      2 ≤ k → 2 ≤ t → BookAdmissible q x y μ r ℓ k t G X Y →
        HasBookStep q x y μ r ℓ k t G X Y) :
    ∀ {k t : ℕ} {X Y : Finset V},
      0 < k → 0 < t → BookAdmissible q x y μ r ℓ k t G X Y →
        Candidate.IsGood G X Y k ℓ t := by
  intro k t X Y hk ht hadm
  induction hsum : k + t using Nat.strong_induction_on generalizing k t X Y with
  | h n ih =>
      rcases hadm with ⟨hC, hd, hm⟩
      by_cases hk1 : k = 1
      · subst k
        exact hC.isGood_one_red ℓ t
      by_cases ht1 : t = 1
      · subst t
        exact hC.isGood_one_blue_left k ℓ
      have hk2 : 2 ≤ k := by omega
      have ht2 : 2 ≤ t := by omega
      have hadm' : BookAdmissible q x y μ r ℓ k t G X Y := ⟨hC, hd, hm⟩
      rcases hstep hk2 ht2 hadm' with
        hgood | ⟨k', t', X', Y', hk', ht', hlt, hchild, hlift⟩
      · exact hgood
      · apply hlift
        exact ih (k' + t') (by omega) (k := k') (t := t')
          (X := X') (Y := Y') hk' ht' hchild rfl

/-- A red-neighborhood child is a valid abstract recursive step. -/
theorem hasBookStep_of_redChild
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ k t : ℕ}
    {X Y X' Y' : Finset V} {v : V}
    (hk : 2 ≤ k) (ht : 0 < t)
    (hchild : BookAdmissible q x y μ r ℓ (k - 1) t G X' Y')
    (hneighbor : X' ∪ Y' ⊆ G.neighborFinset v)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hv : v ∈ X) :
    HasBookStep q x y μ r ℓ k t G X Y := by
  right
  refine ⟨k - 1, t, X', Y', by omega, ht, by omega, hchild, ?_⟩
  intro hgood
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
    Candidate.IsGood.of_red_extension hgood hneighbor hX hY hv

/-- A blue-neighborhood child is a valid abstract recursive step. -/
theorem hasBookStep_of_blueChild
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ k t : ℕ}
    {X Y X' Y' : Finset V} {v : V}
    (hk : 0 < k) (ht : 2 ≤ t)
    (hchild : BookAdmissible q x y μ r ℓ k (t - 1) G X' Y')
    (hneighbor : X' ⊆ Gᶜ.neighborFinset v)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hv : v ∈ X) :
    HasBookStep q x y μ r ℓ k t G X Y := by
  right
  refine ⟨k, t - 1, X', Y', hk, by omega, by omega, hchild, ?_⟩
  intro hgood
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using
    Candidate.IsGood.of_blue_extension_left hgood hneighbor hX hY hv

/-- The pages of a blue book give a recursive child with blue parameter
reduced by the spine size. -/
theorem hasBookStep_of_blueBookChild
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ k t b : ℕ}
    {X Y S T : Finset V}
    (hk : 0 < k) (hb : 0 < b) (hbt : b < t)
    (hbook : BlueBook G S T) (hST : S ∪ T ⊆ X) (hS : #S = b)
    (hchild : BookAdmissible q x y μ r ℓ k (t - b) G T Y) :
    HasBookStep q x y μ r ℓ k t G X Y := by
  right
  refine ⟨k, t - b, T, Y, hk, by omega, by omega, hchild, ?_⟩
  intro hgood
  exact Candidate.IsGood.of_blueBook_extension hbook hgood hST hS hbt.le

/-- A recursive step found after shrinking the left side remains a step for
the original candidate. -/
theorem HasBookStep.mono_left
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ k t : ℕ}
    {X₀ X Y : Finset V} (hsub : X₀ ⊆ X)
    (hstep : HasBookStep q x y μ r ℓ k t G X₀ Y) :
    HasBookStep q x y μ r ℓ k t G X Y := by
  rcases hstep with hgood | ⟨k', t', X', Y', hk', ht', hlt, hchild, hlift⟩
  · exact Or.inl (hgood.mono hsub Finset.Subset.rfl)
  · right
    refine ⟨k', t', X', Y', hk', ht', hlt, hchild, ?_⟩
    intro hgood
    exact (hlift hgood).mono hsub Finset.Subset.rfl

/-! ### Finite child construction and moment transport -/

/-- The target loses one inverse `x` factor in a red step. -/
theorem bookTarget_red_pred {x y μ : ℝ} (hx : x ≠ 0)
    {ℓ k t : ℕ} (hk : 0 < k) :
    bookTarget x y μ ℓ (k - 1) t = x * bookTarget x y μ ℓ k t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.add_one_sub_one, bookTarget, pow_succ]
  field_simp

/-- The target loses one inverse `μ` factor in a blue step. -/
theorem bookTarget_blue_pred {x y μ : ℝ} (hμ : μ ≠ 0)
    {ℓ k t : ℕ} (ht : 0 < t) :
    bookTarget x y μ ℓ k (t - 1) = μ * bookTarget x y μ ℓ k t := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  simp only [Nat.add_one_sub_one, bookTarget, pow_succ]
  field_simp

omit [DecidableEq V] in
/-- Abstract algebra behind both one-vertex moment transfers. -/
theorem bookMoment_child_ge
    {qParent qChild z ρ : ℝ} {r : ℕ}
    {X Y Xc Y' : Finset V}
    (hz : 0 ≤ z) (_hρ : 0 < ρ)
    (hparent : 0 ≤ redDensity G X Y - qParent)
    (hselected : redDensity G X Y - qParent ≤
      redDensity G X Y' - qChild)
    (hchild : 0 ≤ redDensity G Xc Y' - qChild)
    (hside :
      z * (redDensity G X Y' - qChild) ^ r * (#X : ℝ) ≤
        ρ * (redDensity G Xc Y' - qChild) ^ r * (#Xc : ℝ))
    (hright : ρ * (#Y : ℝ) ≤ (#Y' : ℝ)) :
    z * bookMoment qParent r G X Y ≤ bookMoment qChild r G Xc Y' := by
  have hselected_nonneg : 0 ≤ redDensity G X Y' - qChild :=
    hparent.trans hselected
  have hpow :
      (redDensity G X Y - qParent) ^ r ≤
        (redDensity G X Y' - qChild) ^ r :=
    pow_le_pow_left₀ hparent hselected r
  have hfirst :
      z * (redDensity G X Y - qParent) ^ r * (#X : ℝ) ≤
        z * (redDensity G X Y' - qChild) ^ r * (#X : ℝ) := by
    gcongr
  have hside' :
      z * (redDensity G X Y - qParent) ^ r * (#X : ℝ) ≤
        ρ * (redDensity G Xc Y' - qChild) ^ r * (#Xc : ℝ) :=
    hfirst.trans hside
  rw [bookMoment, bookMoment]
  calc
    z * ((redDensity G X Y - qParent) ^ r * (#X : ℝ) * (#Y : ℝ)) =
        (z * (redDensity G X Y - qParent) ^ r * (#X : ℝ)) * (#Y : ℝ) := by ring
    _ ≤ (ρ * (redDensity G Xc Y' - qChild) ^ r * (#Xc : ℝ)) * (#Y : ℝ) := by
      gcongr
    _ = ((redDensity G Xc Y' - qChild) ^ r * (#Xc : ℝ)) *
        (ρ * (#Y : ℝ)) := by ring
    _ ≤ ((redDensity G Xc Y' - qChild) ^ r * (#Xc : ℝ)) * (#Y' : ℝ) := by
      gcongr
    _ = (redDensity G Xc Y' - qChild) ^ r * (#Xc : ℝ) * (#Y' : ℝ) := by ring

theorem redNeighborhoodChild_neighbor_subset {X Y : Finset V} {v : V} :
    (G.neighborFinset v ∩ X) ∪ (G.neighborFinset v ∩ Y) ⊆
      G.neighborFinset v := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact (Finset.mem_inter.mp hw).1
  · exact (Finset.mem_inter.mp hw).1

theorem blueNeighborhoodChild_neighbor_subset {X : Finset V} {v : V} :
    Gᶜ.neighborFinset v ∩ X ⊆ Gᶜ.neighborFinset v :=
  Finset.inter_subset_left

/-- Red and blue neighbors of `v` inside `X` are disjoint, so their cards sum
to at most `#X`. -/
theorem card_red_blue_neighbors_le {X : Finset V} {v : V} :
    #(G.neighborFinset v ∩ X) + #(Gᶜ.neighborFinset v ∩ X) ≤ #X := by
  let R := G.neighborFinset v ∩ X
  let B := Gᶜ.neighborFinset v ∩ X
  have hdisj : Disjoint R B := by
    rw [Finset.disjoint_left]
    intro w hwR hwB
    have hred : G.Adj v w :=
      (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hwR).1
    have hblue : Gᶜ.Adj v w :=
      (Gᶜ.mem_neighborFinset v w).mp (Finset.mem_inter.mp hwB).1
    exact ((G.compl_adj v w).mp hblue).2 hred
  have hsub : R ∪ B ⊆ X :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub

/-- Partitioning `X \ {v}` into red and blue neighbors gives the affine
moment inequality used in equation `(e:moment2)`. Empty children are allowed. -/
theorem density_split_red_blue
    {q : ℝ} (hq : 0 ≤ q) {X Y' : Finset V} {v : V} (hv : v ∈ X)
    (hY' : Y' ⊆ G.neighborFinset v) :
    (redDensity G X Y' - q) * (#X : ℝ) ≤
      (redDensity G (G.neighborFinset v ∩ X) Y' - q) *
          (#(G.neighborFinset v ∩ X) : ℝ) +
        (redDensity G (Gᶜ.neighborFinset v ∩ X) Y' - q) *
          (#(Gᶜ.neighborFinset v ∩ X) : ℝ) + 1 := by
  by_cases hYne : Y'.Nonempty
  · have hraw := redBluePartition_moment2_unnormalized
      (G := G) (X := X) (Y := Y') (v := v) hq hv
    have hY'pos : (0 : ℝ) < #Y' := by exact_mod_cast hYne.card_pos
    have hinter : G.neighborFinset v ∩ Y' = Y' :=
      Finset.inter_eq_right.mpr hY'
    apply le_of_mul_le_mul_right _ hY'pos
    simpa [hinter, mul_assoc] using hraw
  · rw [Finset.not_nonempty_iff_eq_empty.mp hYne]
    simp only [redDensity_empty_right]
    have hcardNat := card_red_blue_neighbors_le (G := G) (X := X) (v := v)
    have hcard :
        (#(G.neighborFinset v ∩ X) : ℝ) +
            (#(Gᶜ.neighborFinset v ∩ X) : ℝ) ≤ (#X : ℝ) := by
      exact_mod_cast hcardNat
    nlinarith

omit [Fintype V] [DecidableEq V] in
private theorem redDensity_mul_card_all' (A B : Finset V) :
    redDensity G A B * ((#A : ℝ) * (#B : ℝ)) = redInteredgeCount G A B := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · exact redDensity_mul_card hA hB
    · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
      simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- Hereditary density on the regularized left side gives the pointwise red
degree bound used for the selected vertex's right neighborhood. -/
theorem card_redNeighborhood_ge_of_hereditary
    {q : ℝ} {X Y : Finset V}
    (hhereditary : ∀ {C : Finset V}, C.Nonempty → C ⊆ X →
      q ≤ redDensity G C Y)
    {v : V} (hv : v ∈ X) :
    q * (#Y : ℝ) ≤ (#(G.neighborFinset v ∩ Y) : ℝ) := by
  have hd : q ≤ redDensity G {v} Y :=
    hhereditary (by simp) (by simpa using hv)
  have hmul := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ #Y by positivity)
  have hcount := redDensity_mul_card_all' (G := G) ({v} : Finset V) Y
  have hinter : redInteredgeCount G {v} Y = #(G.neighborFinset v ∩ Y) := by
    rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
    simp
  simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hcount
  rw [hcount, hinter] at hmul
  exact hmul

/-- Weighted averaging outside a small exceptional set, derived from
`l:FpAvg2` and the public exceptional-set selector. -/
theorem exists_vertex_restrictedDensity_ge
    {X Y W : Finset V} (hC : Candidate G X Y) (hWX : W ⊆ X)
    {ρ η : ℝ} (_hρ : 0 < ρ) (hη : 0 ≤ η) (hηρ : η < ρ)
    (hρd : ρ ≤ redDensity G X Y)
    (hWcard : (#W : ℝ) ≤ η * ρ * (#X : ℝ)) :
    ∃ v ∈ X, v ∉ W ∧
      (G.neighborFinset v ∩ Y).Nonempty ∧
      redDensity G X Y - η ≤
        redDensity G X (G.neighborFinset v ∩ Y) := by
  have hηd : η < redDensity G X Y := hηρ.trans_le hρd
  have hsum := sum_density_mul_card_redNeighborhood_le_card_mul
    (G := G) (X := X) (Y := Y) W
  have hcount := hC.redDensity_mul_card
  have hexception :
      ∑ w ∈ W,
          redDensity G X (G.neighborFinset w ∩ Y) *
            (#(G.neighborFinset w ∩ Y) : ℝ) ≤
        η * (redInteredgeCount G X Y : ℝ) := by
    calc
      ∑ w ∈ W,
          redDensity G X (G.neighborFinset w ∩ Y) *
            (#(G.neighborFinset w ∩ Y) : ℝ) ≤
          (#W : ℝ) * (#Y : ℝ) := hsum
      _ ≤ (η * ρ * (#X : ℝ)) * (#Y : ℝ) := by gcongr
      _ = η * (ρ * ((#X : ℝ) * (#Y : ℝ))) := by ring
      _ ≤ η * (redDensity G X Y * ((#X : ℝ) * (#Y : ℝ))) := by
        gcongr
      _ = η * (redInteredgeCount G X Y : ℝ) := by rw [hcount]
  rcases exists_mem_sdiff_density_redNeighborhood_ge hC hWX hη hηd
      hexception with ⟨v, hv, hselected⟩
  have hrestricted :
      0 < redDensity G X (G.neighborFinset v ∩ Y) :=
    (sub_pos.mpr hηd).trans_le hselected
  have hY' : (G.neighborFinset v ∩ Y).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hrestricted
    simp at hrestricted
  exact ⟨v, (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2,
    hY', hselected⟩

omit [DecidableEq V] in
/-- Assemble admissibility of a red child once the scalar moment transfer has
been established. -/
theorem bookAdmissible_redChild
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ k t : ℕ}
    {X Y Xr Y' : Finset V}
    (hx : 0 < x) (hk : 0 < k)
    (hC : Candidate G Xr Y')
    (hd : q ((k - 1) + t) ≤ redDensity G Xr Y')
    (hparent : bookTarget x y μ ℓ k t ≤
      bookMoment (q (k + t)) r G X Y)
    (hgain : x * bookMoment (q (k + t)) r G X Y ≤
      bookMoment (q ((k - 1) + t)) r G Xr Y') :
    BookAdmissible q x y μ r ℓ (k - 1) t G Xr Y' := by
  refine ⟨hC, hd, ?_⟩
  rw [bookTarget_red_pred hx.ne' hk]
  exact (mul_le_mul_of_nonneg_left hparent hx.le).trans hgain

omit [DecidableEq V] in
/-- Assemble admissibility of a blue child once the scalar moment transfer has
been established. -/
theorem bookAdmissible_blueChild
    {q : ℕ → ℝ} {x y μ : ℝ} {r ℓ k t : ℕ}
    {X Y Xb Y' : Finset V}
    (hμ : μ ≠ 0) (hμnonneg : 0 ≤ μ) (ht : 0 < t)
    (hC : Candidate G Xb Y')
    (hd : q (k + (t - 1)) ≤ redDensity G Xb Y')
    (hparent : bookTarget x y μ ℓ k t ≤
      bookMoment (q (k + t)) r G X Y)
    (hgain : μ * bookMoment (q (k + t)) r G X Y ≤
      bookMoment (q (k + (t - 1))) r G Xb Y') :
    BookAdmissible q x y μ r ℓ k (t - 1) G Xb Y' := by
  refine ⟨hC, hd, ?_⟩
  rw [bookTarget_blue_pred hμ ht]
  exact (mul_le_mul_of_nonneg_left hparent hμnonneg).trans hgain

/-! ### Pure numerical interface for a finite induction step -/

/-- Numerical choices made once before the graph induction. -/
structure BookInductionData where
  p : ℝ
  x : ℝ
  y : ℝ
  μ : ℝ
  densityFloor : ℝ
  highBlueRate : ℝ
  exponent : ℕ
  rightTarget : ℕ
  q : ℕ → ℝ
  averagingLoss : ℕ → ℝ
  localGap : ℕ → ℝ
  blueBookGap : ℕ → ℝ
  spineSize : ℕ → ℕ
  pageCliqueSize : ℕ → ℕ
  minLeftSize : ℕ → ℕ
  rightRamseyScale : ℕ → ℝ

/-- Pure numerical obligations needed by a finite proof of the book step.
No graph, vertex type, or candidate occurs in this record. -/
structure BookInductionBounds (s : BookInductionData) : Prop where
  exponent_pos : 0 < s.exponent
  x_pos : 0 < s.x
  y_pos : 0 < s.y
  μ_pos : 0 < s.μ
  densityFloor_pos : 0 < s.densityFloor
  highBlueRate_pos : 0 < s.highBlueRate
  highBlueRate_lt_one : s.highBlueRate < 1
  q_floor : ∀ n, 2 ≤ n → s.densityFloor ≤ s.q n
  q_le_one : ∀ n, 2 ≤ n → s.q n ≤ 1
  averagingLoss_nonneg : ∀ n, 0 ≤ s.averagingLoss n
  averagingLoss_lt_floor : ∀ n, 4 ≤ n →
    s.averagingLoss n < s.densityFloor
  localGap_pos : ∀ n, 4 ≤ n → 0 < s.localGap n
  blueBookGap_nonneg : ∀ n, 4 ≤ n → 0 ≤ s.blueBookGap n
  local_density_gain : ∀ n, 4 ≤ n →
    s.averagingLoss n + s.localGap n ≤ s.q n - s.q (n - 1)
  spine_pos : ∀ n, 4 ≤ n → 0 < s.spineSize n
  pageClique_pos : ∀ n, 4 ≤ n → 0 < s.pageCliqueSize n
  blueBook_scale : ∀ n, 4 ≤ n →
    10 * (s.spineSize n : ℝ) ^ 2 ≤
      s.highBlueRate * (s.pageCliqueSize n : ℝ)
  minLeft_blueBook : ∀ n, 4 ≤ n →
    5 * (s.pageCliqueSize n) ^ 2 ≤ s.minLeftSize n
  right_ramsey : ∀ k, 0 < k →
    (ramseyNumber k s.rightTarget : ℝ) ≤ s.rightRamseyScale k
  left_large : ∀ {n k t : ℕ} {NX NY d : ℝ},
    n = k + t → 2 ≤ k → 2 ≤ t →
    0 < NX → 0 < NY →
    s.q n ≤ d → d ≤ 1 →
    bookTarget s.x s.y s.μ s.rightTarget k t ≤
      (d - s.q n) ^ s.exponent * NX * NY →
    NY < s.rightRamseyScale k →
    (s.minLeftSize n : ℝ) ≤ NX
  small_high_blue : ∀ {n k t : ℕ},
    n = k + t → 2 ≤ k → 2 ≤ t →
    (ramseyNumber k (s.pageCliqueSize n) : ℝ) ≤
      s.averagingLoss n * s.densityFloor * (s.minLeftSize n : ℝ)
  blueBook_q_gain : ∀ n, 4 ≤ n → s.spineSize n < n →
    s.blueBookGap n ≤ s.q n - s.q (n - s.spineSize n)
  blueBook_moment_gain : ∀ {n k t : ℕ},
    n = k + t → 2 ≤ k → 2 ≤ t → s.spineSize n < t →
    bookTarget s.x s.y s.μ s.rightTarget k (t - s.spineSize n) ≤
      (s.blueBookGap n) ^ s.exponent *
        (s.highBlueRate ^ s.spineSize n / 2) *
          bookTarget s.x s.y s.μ s.rightTarget k t
  local_dichotomy : ∀ {n : ℕ} {NX NR NB α αR αB : ℝ},
    4 ≤ n →
    (s.minLeftSize n : ℝ) ≤ NX →
    s.localGap n ≤ α →
    0 ≤ NR → 0 ≤ NB → NR + NB ≤ NX →
    NB ≤ s.highBlueRate * NX →
    α * NX ≤ αR * NR + αB * NB + 1 →
    (0 ≤ αR ∧
      s.x * α ^ s.exponent * NX ≤
        s.densityFloor * αR ^ s.exponent * NR) ∨
    (0 ≤ αB ∧
      s.μ * α ^ s.exponent * NX ≤
        s.densityFloor * αB ^ s.exponent * NB)

/-- A right side exceeding the certified Ramsey scale is immediately good. -/
theorem hasBookStep_of_largeRight
    {s : BookInductionData} (hs : BookInductionBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 0 < k)
    (hY : s.rightRamseyScale k ≤ (#Y : ℝ)) :
    HasBookStep s.q s.x s.y s.μ s.exponent s.rightTarget k t G X Y := by
  left
  apply Candidate.IsGood.of_ramseyNumber_le_card_right
  exact_mod_cast (hs.right_ramsey k hk).trans hY

omit [DecidableEq V] in
/-- If the right-side terminal branch fails, the parent moment forces the
left side above the scale required by the finite blue-book argument. -/
theorem minLeftSize_le_card_of_rightSmall
    {s : BookInductionData} (hs : BookInductionBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hadm : BookAdmissible s.q s.x s.y s.μ s.exponent
      s.rightTarget k t G X Y)
    (hY : (#Y : ℝ) < s.rightRamseyScale k) :
    s.minLeftSize (k + t) ≤ #X := by
  have hXpos : (0 : ℝ) < (#X : ℝ) := by
    exact_mod_cast hadm.1.left_card_pos
  have hYpos : (0 : ℝ) < (#Y : ℝ) := by
    exact_mod_cast hadm.1.right_card_pos
  have hreal : (s.minLeftSize (k + t) : ℝ) ≤ (#X : ℝ) :=
    hs.left_large rfl hk ht hXpos hYpos
      hadm.2.1 (redDensity_le_one (G := G) X Y)
      (by simpa [bookMoment] using hadm.2.2) hY
  exact_mod_cast hreal

/-- Degree regularization preserves the full abstract induction invariant and
adds the hereditary density property used for arbitrary blue-book pages. -/
theorem exists_regularizedBookAdmissible
    {s : BookInductionData} {k t : ℕ} {X Y : Finset V}
    (hadm : BookAdmissible s.q s.x s.y s.μ s.exponent
      s.rightTarget k t G X Y)
    (hr : 0 < s.exponent) :
    ∃ X₀ : Finset V,
      X₀ ⊆ X ∧
      (∀ {C : Finset V}, C.Nonempty → C ⊆ X₀ →
        s.q (k + t) ≤ redDensity G C Y) ∧
      BookAdmissible s.q s.x s.y s.μ s.exponent
        s.rightTarget k t G X₀ Y := by
  rcases exists_redDegreeRegularized hadm.1 hadm.2.1 hr with
    ⟨X₀, hC, hsub, hhereditary, hmoment⟩
  refine ⟨X₀, hsub, ?_, hC, ?_, ?_⟩
  · intro C hCnonempty hCX₀
    exact hhereditary hCnonempty hCX₀
  · exact hhereditary hC.left_nonempty Finset.Subset.rfl
  · exact hadm.2.2.trans hmoment

/-- The entire many-high-blue branch, including construction of the page
candidate and transfer of its moment, follows from the pure scale bounds. -/
theorem hasBookStep_of_manyHighBlue
    {s : BookInductionData} (hs : BookInductionBounds s)
    {k t : ℕ} {X Y : Finset V}
    (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hadm : BookAdmissible s.q s.x s.y s.μ s.exponent
      s.rightTarget k t G X Y)
    (hhereditary : ∀ {C : Finset V}, C.Nonempty → C ⊆ X →
      s.q (k + t) ≤ redDensity G C Y)
    (hlarge : s.minLeftSize (k + t) ≤ #X)
    (hmany : ramseyNumber k (s.pageCliqueSize (k + t)) ≤
      #(highBlueVertices G X s.highBlueRate)) :
    HasBookStep s.q s.x s.y s.μ s.exponent s.rightTarget k t G X Y := by
  classical
  let n := k + t
  let b := s.spineSize n
  let m := s.pageCliqueSize n
  have hn : 4 ≤ n := by omega
  have hb : 0 < b := hs.spine_pos n hn
  have hm : 0 < m := hs.pageClique_pos n hn
  have hXcard : 5 * m ^ 2 ≤ #X :=
    (hs.minLeft_blueBook n hn).trans hlarge
  rcases exists_redClique_or_blueBook
      hs.highBlueRate_pos hs.highBlueRate_lt_one hb (by omega) hm
      (hs.blueBook_scale n hn) hXcard hmany with
    hred | ⟨S, T, hbook, hST, hS, hTsize⟩
  · left
    exact Candidate.IsGood.of_red
      (hasRedClique_mono Finset.subset_union_left hred)
  · by_cases htb : t ≤ b
    · left
      apply Candidate.IsGood.of_blue_left
      apply hasBlueClique_mono (Finset.subset_union_left.trans hST)
      apply hbook.hasBlueClique_spine_of_le
      simpa [hS] using htb
    · have hbt : b < t := Nat.lt_of_not_ge htb
      have hTsub : T ⊆ X := Finset.subset_union_right.trans hST
      have hXpos : (0 : ℝ) < (#X : ℝ) := by
        exact_mod_cast hadm.1.left_card_pos
      have hratepow : 0 < s.highBlueRate ^ b :=
        pow_pos hs.highBlueRate_pos b
      have hTposReal : (0 : ℝ) < (#T : ℝ) := by
        apply lt_of_lt_of_le _ hTsize
        positivity
      have hT : T.Nonempty := by
        rw [← Finset.card_pos]
        exact_mod_cast hTposReal
      have hTC : Candidate G T Y :=
        hadm.1.subcandidate hTsub Finset.Subset.rfl hT hadm.1.right_nonempty
      have hgap0 : 0 ≤ s.blueBookGap n := hs.blueBookGap_nonneg n hn
      have hqgain :
          s.blueBookGap n ≤ s.q n - s.q (n - b) :=
        hs.blueBook_q_gain n hn (by omega)
      have hqmono : s.q (n - b) ≤ s.q n := by linarith
      have hTYdensity : s.q (n - b) ≤ redDensity G T Y :=
        hqmono.trans (hhereditary hT hTsub)
      have hparentBase : 0 ≤ redDensity G X Y - s.q n := by
        exact sub_nonneg.mpr hadm.2.1
      have hqn0 : 0 ≤ s.q n :=
        hs.densityFloor_pos.le.trans (hs.q_floor n (by omega))
      have hparentBase_le : redDensity G X Y - s.q n ≤ 1 := by
        linarith [redDensity_le_one (G := G) X Y]
      have hparentPow_le : (redDensity G X Y - s.q n) ^ s.exponent ≤ 1 := by
        simpa using pow_le_pow_left₀ hparentBase hparentBase_le s.exponent
      have hparentMoment_le :
          bookMoment (s.q n) s.exponent G X Y ≤ (#X : ℝ) * (#Y : ℝ) := by
        rw [bookMoment]
        calc
          (redDensity G X Y - s.q n) ^ s.exponent * (#X : ℝ) * (#Y : ℝ) ≤
              1 * (#X : ℝ) * (#Y : ℝ) := by gcongr
          _ = (#X : ℝ) * (#Y : ℝ) := by ring
      have htarget_parent :
          bookTarget s.x s.y s.μ s.rightTarget k t ≤
            (#X : ℝ) * (#Y : ℝ) :=
        hadm.2.2.trans hparentMoment_le
      have hchildBase :
          s.blueBookGap n ≤ redDensity G T Y - s.q (n - b) := by
        linarith [hhereditary hT hTsub]
      have hchildBase0 : 0 ≤ redDensity G T Y - s.q (n - b) :=
        sub_nonneg.mpr hTYdensity
      have hpowGain :
          (s.blueBookGap n) ^ s.exponent ≤
            (redDensity G T Y - s.q (n - b)) ^ s.exponent :=
        pow_le_pow_left₀ hgap0 hchildBase s.exponent
      have htarget_child :
          bookTarget s.x s.y s.μ s.rightTarget k (t - b) ≤
            bookMoment (s.q (k + (t - b))) s.exponent G T Y := by
        have hnchild : k + (t - b) = n - b := by omega
        rw [hnchild]
        calc
          bookTarget s.x s.y s.μ s.rightTarget k (t - b) ≤
              (s.blueBookGap n) ^ s.exponent *
                (s.highBlueRate ^ b / 2) *
                  bookTarget s.x s.y s.μ s.rightTarget k t := by
                    exact hs.blueBook_moment_gain (n := n) (k := k) (t := t)
                      rfl hk ht hbt
          _ ≤ (s.blueBookGap n) ^ s.exponent *
                (s.highBlueRate ^ b / 2) * ((#X : ℝ) * (#Y : ℝ)) := by
                    gcongr
          _ ≤ (s.blueBookGap n) ^ s.exponent * (#T : ℝ) * (#Y : ℝ) := by
                    calc
                      (s.blueBookGap n) ^ s.exponent *
                            (s.highBlueRate ^ b / 2) *
                            ((#X : ℝ) * (#Y : ℝ)) =
                          (s.blueBookGap n) ^ s.exponent *
                            ((s.highBlueRate ^ b / 2) * (#X : ℝ)) *
                            (#Y : ℝ) := by ring
                      _ ≤ (s.blueBookGap n) ^ s.exponent * (#T : ℝ) *
                            (#Y : ℝ) := by gcongr
          _ ≤ (redDensity G T Y - s.q (n - b)) ^ s.exponent *
                (#T : ℝ) * (#Y : ℝ) := by
                    gcongr
          _ = bookMoment (s.q (n - b)) s.exponent G T Y := by
                    rw [bookMoment]
      have hchild :
          BookAdmissible s.q s.x s.y s.μ s.exponent s.rightTarget
            k (t - b) G T Y := by
        refine ⟨hTC, ?_, htarget_child⟩
        rw [show k + (t - b) = n - b by omega]
        exact hTYdensity
      exact hasBookStep_of_blueBookChild (by omega) hb hbt hbook hST hS hchild

/-- Once weighted averaging supplies a low-blue vertex with almost-preserved
restricted density, the local numerical dichotomy forces either the red or
the blue recursive child.  All candidate construction and both exact moment
transfers are discharged here. -/
theorem hasBookStep_of_selectedVertex
    {s : BookInductionData} (hs : BookInductionBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hadm : BookAdmissible s.q s.x s.y s.μ s.exponent
      s.rightTarget k t G X Y)
    (hhereditary : ∀ {C : Finset V}, C.Nonempty → C ⊆ X →
      s.q (k + t) ≤ redDensity G C Y)
    (hlarge : s.minLeftSize (k + t) ≤ #X)
    {v : V} (hv : v ∈ X)
    (hlowBlue : (#(Gᶜ.neighborFinset v ∩ X) : ℝ) ≤
      s.highBlueRate * (#X : ℝ))
    (hselected : redDensity G X Y - s.averagingLoss (k + t) ≤
      redDensity G X (G.neighborFinset v ∩ Y)) :
    HasBookStep s.q s.x s.y s.μ s.exponent s.rightTarget k t G X Y := by
  classical
  let n := k + t
  let qParent := s.q n
  let qChild := s.q (n - 1)
  let Y' := G.neighborFinset v ∩ Y
  let Xr := G.neighborFinset v ∩ X
  let Xb := Gᶜ.neighborFinset v ∩ X
  let α := redDensity G X Y' - qChild
  let αR := redDensity G Xr Y' - qChild
  let αB := redDensity G Xb Y' - qChild
  have hn : 4 ≤ n := by omega
  have hnchild : 2 ≤ n - 1 := by omega
  have hqParentFloor : s.densityFloor ≤ qParent := hs.q_floor n (by omega)
  have hqChildFloor : s.densityFloor ≤ qChild := hs.q_floor (n - 1) hnchild
  have hqParent0 : 0 ≤ qParent := hs.densityFloor_pos.le.trans hqParentFloor
  have hqChild0 : 0 ≤ qChild := hs.densityFloor_pos.le.trans hqChildFloor
  have hparentBase : 0 ≤ redDensity G X Y - qParent := by
    exact sub_nonneg.mpr hadm.2.1
  have hlocalGain := hs.local_density_gain n hn
  have hlocalGap0 : 0 ≤ s.localGap n := (hs.localGap_pos n hn).le
  have hselected' :
      redDensity G X Y - s.averagingLoss n ≤ redDensity G X Y' := by
    simpa [n, Y'] using hselected
  have hselectedBase :
      redDensity G X Y - qParent ≤ α := by
    dsimp [α, qParent, qChild]
    linarith
  have hαgap : s.localGap n ≤ α := by
    dsimp [α, qParent, qChild]
    have hdensity : s.q n ≤ redDensity G X Y := by simpa [n] using hadm.2.1
    linarith
  have hrightQ : qParent * (#Y : ℝ) ≤ (#Y' : ℝ) := by
    dsimp [qParent, Y', n]
    exact card_redNeighborhood_ge_of_hereditary hhereditary hv
  have hright : s.densityFloor * (#Y : ℝ) ≤ (#Y' : ℝ) := by
    calc
      s.densityFloor * (#Y : ℝ) ≤ qParent * (#Y : ℝ) := by gcongr
      _ ≤ (#Y' : ℝ) := hrightQ
  have hcards : (#Xr : ℝ) + (#Xb : ℝ) ≤ (#X : ℝ) := by
    exact_mod_cast card_red_blue_neighbors_le (G := G) (X := X) (v := v)
  have hsplit :
      α * (#X : ℝ) ≤
        αR * (#Xr : ℝ) + αB * (#Xb : ℝ) + 1 := by
    dsimp [α, αR, αB, Xr, Xb, Y', qChild]
    exact density_split_red_blue hqChild0 hv Finset.inter_subset_left
  have hlargeReal : (s.minLeftSize n : ℝ) ≤ (#X : ℝ) := by
    exact_mod_cast hlarge
  rcases hs.local_dichotomy hn hlargeReal hαgap
      (by positivity : (0 : ℝ) ≤ #Xr) (by positivity : (0 : ℝ) ≤ #Xb)
      hcards (by simpa [Xb, n] using hlowBlue) hsplit with
    ⟨hαR, hredSide⟩ | ⟨hαB, hblueSide⟩
  · have hdR : qChild ≤ redDensity G Xr Y' := sub_nonneg.mp hαR
    have hdRpos : 0 < redDensity G Xr Y' :=
      hs.densityFloor_pos.trans_le (hqChildFloor.trans hdR)
    have hCR : Candidate G Xr Y' :=
      hadm.1.subcandidate_of_redDensity_pos Finset.inter_subset_right
        Finset.inter_subset_right hdRpos
    have hmomentGain :
        s.x * bookMoment qParent s.exponent G X Y ≤
          bookMoment qChild s.exponent G Xr Y' := by
      exact bookMoment_child_ge hs.x_pos.le hs.densityFloor_pos
        hparentBase hselectedBase hαR hredSide hright
    have hidx : (k - 1) + t = n - 1 := by omega
    have hchild :
        BookAdmissible s.q s.x s.y s.μ s.exponent s.rightTarget
          (k - 1) t G Xr Y' := by
      apply bookAdmissible_redChild hs.x_pos (by omega) hCR
      · simpa [qChild, hidx] using hdR
      · simpa [qParent, n] using hadm.2.2
      · simpa [qParent, qChild, n, hidx] using hmomentGain
    apply hasBookStep_of_redChild hk (by omega) hchild
    · exact redNeighborhoodChild_neighbor_subset
    · exact Finset.inter_subset_right
    · exact Finset.inter_subset_right
    · exact hv
  · have hdB : qChild ≤ redDensity G Xb Y' := sub_nonneg.mp hαB
    have hdBpos : 0 < redDensity G Xb Y' :=
      hs.densityFloor_pos.trans_le (hqChildFloor.trans hdB)
    have hCB : Candidate G Xb Y' :=
      hadm.1.subcandidate_of_redDensity_pos Finset.inter_subset_right
        Finset.inter_subset_right hdBpos
    have hmomentGain :
        s.μ * bookMoment qParent s.exponent G X Y ≤
          bookMoment qChild s.exponent G Xb Y' := by
      exact bookMoment_child_ge hs.μ_pos.le hs.densityFloor_pos
        hparentBase hselectedBase hαB hblueSide hright
    have hidx : k + (t - 1) = n - 1 := by omega
    have hchild :
        BookAdmissible s.q s.x s.y s.μ s.exponent s.rightTarget
          k (t - 1) G Xb Y' := by
      apply bookAdmissible_blueChild hs.μ_pos.ne' hs.μ_pos.le (by omega) hCB
      · simpa [qChild, hidx] using hdB
      · simpa [qParent, n] using hadm.2.2
      · simpa [qParent, qChild, n, hidx] using hmomentGain
    apply hasBookStep_of_blueChild (by omega) ht hchild
    · exact blueNeighborhoodChild_neighbor_subset
    · exact Finset.inter_subset_right
    · exact Finset.inter_subset_right
    · exact hv

/-- Dispatcher for one nonterminal induction step.  It regularizes first,
handles the right-side Ramsey terminal branch, and then splits on whether the
high-blue exceptional set is large enough for `l:BBook`. -/
theorem hasBookStep_of_inductionBounds
    {s : BookInductionData} (hs : BookInductionBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hadm : BookAdmissible s.q s.x s.y s.μ s.exponent
      s.rightTarget k t G X Y) :
    HasBookStep s.q s.x s.y s.μ s.exponent s.rightTarget k t G X Y := by
  classical
  rcases exists_regularizedBookAdmissible hadm hs.exponent_pos with
    ⟨X₀, hX₀X, hhereditary, hadm₀⟩
  apply HasBookStep.mono_left hX₀X
  by_cases hYlarge : s.rightRamseyScale k ≤ (#Y : ℝ)
  · exact hasBookStep_of_largeRight hs (by omega) hYlarge
  have hYsmall : (#Y : ℝ) < s.rightRamseyScale k := lt_of_not_ge hYlarge
  have hlarge : s.minLeftSize (k + t) ≤ #X₀ :=
    minLeftSize_le_card_of_rightSmall hs hk ht hadm₀ hYsmall
  let W := highBlueVertices G X₀ s.highBlueRate
  let m := s.pageCliqueSize (k + t)
  by_cases hmany : ramseyNumber k m ≤ #W
  · exact hasBookStep_of_manyHighBlue hs hk ht hadm₀ hhereditary hlarge hmany
  have hWlt : #W < ramseyNumber k m := lt_of_not_ge hmany
  have hWsub : W ⊆ X₀ := by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have hn : 4 ≤ k + t := by omega
  have hWcard :
      (#W : ℝ) ≤ s.averagingLoss (k + t) * s.densityFloor * (#X₀ : ℝ) := by
    calc
      (#W : ℝ) ≤ (ramseyNumber k m : ℝ) := by exact_mod_cast hWlt.le
      _ ≤ s.averagingLoss (k + t) * s.densityFloor *
          (s.minLeftSize (k + t) : ℝ) := by
            exact hs.small_high_blue rfl hk ht
      _ ≤ s.averagingLoss (k + t) * s.densityFloor * (#X₀ : ℝ) := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast hlarge
            · exact mul_nonneg (hs.averagingLoss_nonneg (k + t))
                hs.densityFloor_pos.le
  have hfloorDensity : s.densityFloor ≤ redDensity G X₀ Y :=
    (hs.q_floor (k + t) (by omega)).trans hadm₀.2.1
  rcases exists_vertex_restrictedDensity_ge hadm₀.1 hWsub
      hs.densityFloor_pos (hs.averagingLoss_nonneg (k + t))
      (hs.averagingLoss_lt_floor (k + t) hn) hfloorDensity hWcard with
    ⟨v, hvX₀, hvW, _, hselected⟩
  have hnotHigh :
      ¬s.highBlueRate * (#X₀ : ℝ) ≤
        (#(Gᶜ.neighborFinset v ∩ X₀) : ℝ) := by
    intro hhigh
    apply hvW
    exact Finset.mem_filter.mpr ⟨hvX₀, hhigh⟩
  have hlowBlue :
      (#(Gᶜ.neighborFinset v ∩ X₀) : ℝ) ≤
        s.highBlueRate * (#X₀ : ℝ) :=
    (lt_of_not_ge hnotHigh).le
  exact hasBookStep_of_selectedVertex hs hk ht hadm₀ hhereditary hlarge
    hvX₀ hlowBlue hselected

/-- Complete graph-independent induction conclusion from a package of pure
scale estimates. -/
theorem isGood_of_bookInductionBounds
    {s : BookInductionData} (hs : BookInductionBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 0 < k) (ht : 0 < t)
    (hadm : BookAdmissible s.q s.x s.y s.μ s.exponent
      s.rightTarget k t G X Y) :
    Candidate.IsGood G X Y k s.rightTarget t :=
  bookStrongInductionCore
    (fun hk ht hadm => hasBookStep_of_inductionBounds hs hk ht hadm)
    hk ht hadm

end BookInductionCore
/-! ## Concrete graph-independent induction scales -/

/-- The integer lower-size threshold used by the finite book induction. -/
noncomputable def bookMinimumLeftSize (ε : ℝ) (ℓ n : ℕ) : ℕ :=
  ⌊(1 + ε) ^ (n + ℓ)⌋₊

/-- The right-side Ramsey scale at shifted asymptotic-region coordinates. -/
noncomputable def bookRightRamseyScale (x y ε : ℝ) (ℓ k : ℕ) : ℝ :=
  ((x + ε)⁻¹) ^ k * ((y + ε)⁻¹) ^ ℓ

/-- Concrete numerical data realizing the strengthened book-induction invariant. -/
noncomputable def concreteBookInductionData
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p) (ℓ : ℕ) :
    BookInductionData where
  p := p
  x := x₀ + a.ε
  y := y₀ + a.ε
  μ := μ₀ + a.ε
  densityFloor := p - a.ε
  highBlueRate := μ₀ + 2 * a.ε
  exponent := a.r
  rightTarget := ℓ
  q := fun n => p - a.ε / (n : ℝ)
  averagingLoss := fun n => a.ε / (n : ℝ) ^ 3
  localGap := fun n => a.ε / (n : ℝ) ^ 2
  blueBookGap := fun n => a.ε / (n : ℝ) ^ 2
  spineSize := bookSpineSize a.ε a.r
  pageCliqueSize := fun n => bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n)
  minLeftSize := bookMinimumLeftSize a.ε ℓ
  rightRamseyScale := bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ

private def concreteBookLocalDichotomy (s : BookInductionData) : Prop :=
  ∀ {n : ℕ} {NX NR NB α αR αB : ℝ},
    4 ≤ n →
    (s.minLeftSize n : ℝ) ≤ NX →
    s.localGap n ≤ α →
    0 ≤ NR → 0 ≤ NB → NR + NB ≤ NX →
    NB ≤ s.highBlueRate * NX →
    α * NX ≤ αR * NR + αB * NB + 1 →
    (0 ≤ αR ∧
      s.x * α ^ s.exponent * NX ≤
        s.densityFloor * αR ^ s.exponent * NR) ∨
    (0 ≤ αB ∧
      s.μ * α ^ s.exponent * NX ≤
        s.densityFloor * αB ^ s.exponent * NB)

private theorem density_gain
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    ε / (n : ℝ) ^ 3 + ε / (n : ℝ) ^ 2 ≤
      (ε / ((n - 1 : ℕ) : ℝ)) - ε / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1R : ((0 : ℝ) < (n - 1 : ℕ)) := by exact_mod_cast (by omega : 0 < n - 1)
  have hn0 : (0 : ℝ) < n := by positivity
  have hnminus : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hlhs :
      ε / (n : ℝ) ^ 3 + ε / (n : ℝ) ^ 2 =
        ε * (1 + (n : ℝ)) / (n : ℝ) ^ 3 := by
    field_simp [hn0.ne']
  have hrhs :
      (ε / ((n - 1 : ℕ) : ℝ)) - ε / (n : ℝ) =
        ε / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    field_simp [hn0.ne', hnminus.ne']
    ring
  rw [hlhs, hrhs]
  apply (div_le_div_iff₀ (pow_pos hn0 3) (mul_pos hn0 hnminus)).2
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

private theorem blue_q_gain
    {ε : ℝ} (hε : 0 < ε) {n b : ℕ} (hn : 0 < n) (hb : 0 < b)
    (hbn : b < n) :
    ε / (n : ℝ) ^ 2 ≤
      (ε / ((n - b : ℕ) : ℝ)) - ε / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnbR : (0 : ℝ) < (n - b : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hbn)
  have hbnR : (b : ℝ) < n := by exact_mod_cast hbn
  have hdiff : (0 : ℝ) < (n : ℝ) - (b : ℝ) := by linarith
  have hrhs :
      (ε / ((n - b : ℕ) : ℝ)) - ε / (n : ℝ) =
        ε * (b : ℝ) / ((n : ℝ) * ((n : ℝ) - (b : ℝ))) := by
    rw [Nat.cast_sub (by omega : b ≤ n)]
    field_simp [hnR.ne', hdiff.ne']
    ring
  rw [hrhs]
  apply (div_le_div_iff₀ (pow_pos hnR 2) (mul_pos hnR hdiff)).2
  have hprod : (0 : ℝ) ≤ (n : ℝ) * ((b : ℝ) - 1) :=
    mul_nonneg hnR.le (by linarith)
  nlinarith [sq_nonneg (n : ℝ), mul_nonneg hε.le hprod]

private theorem floor_margin
    {ε E : ℝ} (hε : 0 < ε) (hE : (1 + ε) / ε ≤ E) :
    E / (1 + ε) ≤ (⌊E⌋₊ : ℝ) := by
  have hbase : 0 < 1 + ε := by linarith
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have hfloor : E < (⌊E⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one E
  have hgap : E / (1 + ε) ≤ E - 1 := by
    rw [div_le_iff₀ hbase]
    have hmul : 1 + ε ≤ ε * E := by
      calc
        1 + ε = ε * ((1 + ε) / ε) := by field_simp
        _ ≤ ε * E := mul_le_mul_of_nonneg_left hE hε.le
    nlinarith
  linarith

private theorem scaled_inv_pow_le_inv_pow
    {z ε : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hε : 0 < ε) (n : ℕ) :
    (1 + ε) ^ n * ((z + ε)⁻¹) ^ n ≤ (z⁻¹) ^ n := by
  have hze : 0 < z + ε := add_pos hz hε
  have hbase : (1 + ε) * (z + ε)⁻¹ ≤ z⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hz1 hε.le
    have hdiv : (1 + ε) / (z + ε) ≤ 1 / z :=
      (div_le_div_iff₀ hze hz).2 (by nlinarith)
    simpa [div_eq_mul_inv] using hdiv
  calc
    (1 + ε) ^ n * ((z + ε)⁻¹) ^ n =
        ((1 + ε) * (z + ε)⁻¹) ^ n := (mul_pow _ _ _).symm
    _ ≤ (z⁻¹) ^ n := pow_le_pow_left₀ (by positivity) hbase n

private theorem exponential_mul_bookRightRamseyScale_le_target
    {x y μ ε : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) (hμ : 0 < μ)
    (hε : 0 < ε) (hscale : (1 + ε) * μ ≤ 1)
    (k t ℓ : ℕ) :
    (1 + ε) ^ (k + t + ℓ) * bookRightRamseyScale x y ε ℓ k ≤
      bookTarget x y μ ℓ k t := by
  have hxpow := scaled_inv_pow_le_inv_pow hx hx1 hε k
  have hypow := scaled_inv_pow_le_inv_pow hy hy1 hε ℓ
  have hμbase : 1 + ε ≤ μ⁻¹ := by
    simp only [inv_eq_one_div]
    rw [le_div_iff₀ hμ]
    simpa [mul_comm] using hscale
  have hμpow : (1 + ε) ^ t ≤ (μ⁻¹) ^ t :=
    pow_le_pow_left₀ (by positivity) hμbase t
  simp only [bookRightRamseyScale, bookTarget]
  rw [show k + t + ℓ = k + ℓ + t by omega, pow_add, pow_add]
  calc
    ((1 + ε) ^ k * (1 + ε) ^ ℓ * (1 + ε) ^ t) *
        (((x + ε)⁻¹) ^ k * ((y + ε)⁻¹) ^ ℓ) =
      ((1 + ε) ^ k * ((x + ε)⁻¹) ^ k) *
        ((1 + ε) ^ ℓ * ((y + ε)⁻¹) ^ ℓ) * (1 + ε) ^ t := by ring
    _ ≤ (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ t := by
      gcongr

private theorem exponential_le_floor
    {ε : ℝ} (hε : 0 < ε) {n ℓ : ℕ}
    (hlarge : (1 + ε) / ε ≤ (1 + ε) ^ ℓ) :
    (1 + ε) ^ (n + (ℓ - 1)) ≤
      (bookMinimumLeftSize ε ℓ n : ℝ) := by
  have hbase : 0 < 1 + ε := by linarith
  have hℓ : 0 < ℓ := by
    by_contra h
    have : ℓ = 0 := Nat.eq_zero_of_not_pos h
    subst ℓ
    norm_num at hlarge
    have : 1 < (1 + ε) / ε := by
      rw [one_lt_div hε]
      linarith
    linarith
  have hElarge : (1 + ε) / ε ≤ (1 + ε) ^ (n + ℓ) := by
    calc
      (1 + ε) / ε ≤ (1 + ε) ^ ℓ := hlarge
      _ ≤ (1 + ε) ^ (n + ℓ) := by
        rw [show n + ℓ = ℓ + n by omega, pow_add]
        exact le_mul_of_one_le_right (pow_nonneg hbase.le _)
          (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε))
  have hmargin := floor_margin hε hElarge
  have hpow :
      (1 + ε) ^ (n + (ℓ - 1)) = (1 + ε) ^ (n + ℓ) / (1 + ε) := by
    rw [eq_div_iff hbase.ne']
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  simpa [bookMinimumLeftSize] using hmargin

private theorem concrete_left_large
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) {ℓ n k t : ℕ} {NX NY d : ℝ}
    (hn : n = k + t) (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hNX : 0 < NX) (hNY : 0 < NY)
    (hdlow : p - a.ε / (n : ℝ) ≤ d) (hdhigh : d ≤ 1)
    (hmoment :
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t ≤
        (d - (p - a.ε / (n : ℝ))) ^ a.r * NX * NY)
    (hY : NY < bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ k) :
    (bookMinimumLeftSize a.ε ℓ n : ℝ) ≤ NX := by
  have hn4 : 4 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hεdiv_nonneg : 0 ≤ a.ε / (n : ℝ) := div_nonneg a.ε_pos.le hnR.le
  have hεdiv_le : a.ε / (n : ℝ) ≤ a.ε := by
    rw [div_le_iff₀ hnR]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith [mul_nonneg a.ε_pos.le (sub_nonneg.mpr hn1)]
  have hqpos : 0 < p - a.ε / (n : ℝ) := by
    linarith [a.two_epsilon_lt]
  have hdiff0 : 0 ≤ d - (p - a.ε / (n : ℝ)) := sub_nonneg.mpr hdlow
  have hdiff1 : d - (p - a.ε / (n : ℝ)) ≤ 1 := by linarith
  have hpowle : (d - (p - a.ε / (n : ℝ))) ^ a.r ≤ 1 :=
    pow_le_one₀ hdiff0 hdiff1
  have htarget_le :
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t ≤ NX * NY := by
    calc
      _ ≤ (d - (p - a.ε / (n : ℝ))) ^ a.r * NX * NY := hmoment
      _ ≤ 1 * NX * NY := by gcongr
      _ = NX * NY := by ring
  have hx : 0 < x₀ + a.ε := add_pos hx₀.1 a.ε_pos
  have hy : 0 < y₀ + a.ε := add_pos hy₀.1 a.ε_pos
  have hμ : 0 < μ₀ + a.ε := add_pos hμ₀.1 a.ε_pos
  have hx1 : x₀ + a.ε ≤ 1 := by linarith [a.sum_lt_one, hμ₀.1]
  have hregionUnit := asymptoticRegionInterior_subset_openUnitSquare a.region
  have hy1 : y₀ + a.ε ≤ 1 := by linarith [hregionUnit.2.2, a.ε_pos]
  have hscaleμ : (1 + a.ε) * (μ₀ + a.ε) ≤ 1 := a.scale_mu.le
  have hrightPos : 0 < bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ k := by
    exact mul_pos
      (pow_pos (inv_pos.mpr (add_pos hx a.ε_pos)) _)
      (pow_pos (inv_pos.mpr (add_pos hy a.ε_pos)) _)
  have hscaled := exponential_mul_bookRightRamseyScale_le_target
    hx hx1 hy hy1 hμ a.ε_pos hscaleμ k t ℓ
  rw [← hn] at hscaled
  have hstrict :
      (1 + a.ε) ^ (n + ℓ) *
          bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ k <
        NX * bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ k :=
    hscaled.trans_lt (htarget_le.trans_lt (mul_lt_mul_of_pos_left hY hNX))
  have hENX : (1 + a.ε) ^ (n + ℓ) < NX :=
    by nlinarith
  have hE0 : 0 ≤ (1 + a.ε) ^ (n + ℓ) :=
    pow_nonneg (by linarith [a.ε_pos]) _
  simpa [bookMinimumLeftSize] using
    (Nat.floor_le hE0).trans hENX.le

private theorem concrete_blue_moment_gain
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hμ₀ : 0 < μ₀) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    {L ℓ n k t : ℕ} (hn : n = k + t)
    (hschedule : BookAsymptoticScaleBounds a.ε (μ₀ + 2 * a.ε) p a.r L)
    (hb : bookSpineSize a.ε a.r n < t) :
    bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k
        (t - bookSpineSize a.ε a.r n) ≤
      (a.ε / (n : ℝ) ^ 2) ^ a.r *
        ((μ₀ + 2 * a.ε) ^ bookSpineSize a.ε a.r n / 2) *
          bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t := by
  let b := bookSpineSize a.ε a.r n
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hμ : 0 < μ₀ + a.ε := add_pos hμ₀ a.ε_pos
  have hhigh : 0 < μ₀ + 2 * a.ε := by linarith [hμ₀, a.ε_pos]
  have hratio : (1 + a.ε) * (μ₀ + a.ε) ≤ μ₀ + 2 * a.ε := by
    have hsum := a.sum_lt_one
    have hunit : μ₀ + a.ε ≤ 1 := by linarith [hx₀, a.ε_pos]
    have hmul := mul_le_mul_of_nonneg_left hunit a.ε_pos.le
    nlinarith
  have hratioPow :
      (1 + a.ε) ^ b * (μ₀ + a.ε) ^ b ≤ (μ₀ + 2 * a.ε) ^ b := by
    rw [← mul_pow]
    exact pow_le_pow_left₀
      (mul_nonneg (by linarith [a.ε_pos]) hμ.le) hratio b
  have hgain := hschedule.blue_gain n hnpos
  have hmulGain :
      2 * ((((n : ℝ) ^ 2) / a.ε) ^ a.r) * (μ₀ + a.ε) ^ b ≤
        (μ₀ + 2 * a.ε) ^ b := by
    calc
      _ ≤ (1 + a.ε) ^ b * (μ₀ + a.ε) ^ b := by gcongr
      _ ≤ _ := hratioPow
  have hA : 0 < (a.ε / (n : ℝ) ^ 2) ^ a.r :=
    pow_pos (div_pos a.ε_pos (sq_pos_of_pos hnR)) _
  have hB : 0 < (((n : ℝ) ^ 2 / a.ε) ^ a.r) :=
    pow_pos (div_pos (sq_pos_of_pos hnR) a.ε_pos) _
  have hAB :
      (a.ε / (n : ℝ) ^ 2) ^ a.r *
          (((n : ℝ) ^ 2 / a.ε) ^ a.r) = 1 := by
    rw [← mul_pow]
    have : a.ε / (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 / a.ε) = 1 := by
      field_simp [a.ε_pos.ne', hnR.ne']
    rw [this, one_pow]
  have hscalar :
      (μ₀ + a.ε) ^ b ≤
        (a.ε / (n : ℝ) ^ 2) ^ a.r * ((μ₀ + 2 * a.ε) ^ b / 2) := by
    have heq :
        (a.ε / (n : ℝ) ^ 2) ^ a.r * ((μ₀ + 2 * a.ε) ^ b / 2) =
          (μ₀ + 2 * a.ε) ^ b /
            (2 * (((n : ℝ) ^ 2 / a.ε) ^ a.r)) := by
      rw [eq_div_iff (mul_ne_zero (by norm_num) hB.ne')]
      calc
        (a.ε / (n : ℝ) ^ 2) ^ a.r * ((μ₀ + 2 * a.ε) ^ b / 2) *
            (2 * (((n : ℝ) ^ 2 / a.ε) ^ a.r)) =
          ((a.ε / (n : ℝ) ^ 2) ^ a.r *
            (((n : ℝ) ^ 2 / a.ε) ^ a.r)) * (μ₀ + 2 * a.ε) ^ b := by ring
        _ = (μ₀ + 2 * a.ε) ^ b := by rw [hAB, one_mul]
    rw [heq, le_div_iff₀ (mul_pos (by norm_num) hB)]
    calc
      (μ₀ + a.ε) ^ b * (2 * ((n : ℝ) ^ 2 / a.ε) ^ a.r) =
          2 * ((n : ℝ) ^ 2 / a.ε) ^ a.r * (μ₀ + a.ε) ^ b := by ring
      _ ≤ _ := hmulGain
  have hinv :
      ((μ₀ + a.ε)⁻¹) ^ (t - b) =
        (μ₀ + a.ε) ^ b * ((μ₀ + a.ε)⁻¹) ^ t := by
    conv_rhs =>
      rw [show t = (t - b) + b by omega, pow_add]
    symm
    calc
      (μ₀ + a.ε) ^ b *
          (((μ₀ + a.ε)⁻¹) ^ (t - b) * ((μ₀ + a.ε)⁻¹) ^ b) =
        ((μ₀ + a.ε)⁻¹) ^ (t - b) *
          ((μ₀ + a.ε) ^ b * ((μ₀ + a.ε)⁻¹) ^ b) := by ring
      _ = ((μ₀ + a.ε)⁻¹) ^ (t - b) := by
        rw [← mul_pow, mul_inv_cancel₀ hμ.ne', one_pow, mul_one]
  have htarget :
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k (t - b) =
        (μ₀ + a.ε) ^ b *
          bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t := by
    simp only [bookTarget]
    rw [hinv]
    ring
  rw [show bookSpineSize a.ε a.r n = b by rfl, htarget]
  calc
    (μ₀ + a.ε) ^ b *
        bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t ≤
      ((a.ε / (n : ℝ) ^ 2) ^ a.r * ((μ₀ + 2 * a.ε) ^ b / 2)) *
        bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t :=
      mul_le_mul_of_nonneg_right hscalar (by
        simp only [bookTarget]
        exact mul_nonneg
          (mul_nonneg
            (pow_nonneg (inv_nonneg.mpr (add_pos hx₀ a.ε_pos).le) _)
            (pow_nonneg (inv_nonneg.mpr (add_pos hy₀ a.ε_pos).le) _))
          (pow_nonneg (inv_nonneg.mpr hμ.le) _))
    _ = _ := by ring

private theorem concrete_small_high_blue
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    {L ℓ n k t : ℕ}
    (hschedule : BookAsymptoticScaleBounds a.ε (μ₀ + 2 * a.ε) p a.r L)
    (hLprev : L ≤ ℓ - 1)
    (hlarge : (1 + a.ε) / a.ε ≤ (1 + a.ε) ^ ℓ)
    (hn : n = k + t) (hk : 2 ≤ k) (ht : 2 ≤ t) :
    (ramseyNumber k
        (bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n)) : ℝ) ≤
      (a.ε / (n : ℝ) ^ 3) * (p - a.ε) *
        (bookMinimumLeftSize a.ε ℓ n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hkpos : 0 < k := by omega
  have hmpos : 0 < bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n) :=
    hschedule.page_pos n hnpos
  have hramseyNat := RamseyLean.ramseyNumber_le_pow_first hkpos hmpos
  have hkn : k ≤ n := by omega
  have hramsey :
      (ramseyNumber k
          (bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n)) : ℝ) ≤
        (n : ℝ) ^ (bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n)) := by
    exact_mod_cast hramseyNat.trans (Nat.pow_le_pow_left hkn _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos hnR _
  have hexception := hschedule.exceptional_ramsey n (ℓ - 1) hnpos hLprev
  have hpow :
      (n : ℝ) ^ (bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n)) ≤
        (a.ε * (p - a.ε) / (n : ℝ) ^ 3) *
          (1 + a.ε) ^ (n + (ℓ - 1)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hn3]
    simpa [pow_add, mul_assoc] using hexception
  have hfloor := exponential_le_floor a.ε_pos hlarge (n := n)
  have hcoeff : 0 ≤ a.ε * (p - a.ε) / (n : ℝ) ^ 3 := by
    have hpε : 0 < p - a.ε := by linarith [a.two_epsilon_lt, a.ε_pos]
    exact div_nonneg (mul_nonneg a.ε_pos.le hpε.le) (pow_nonneg hnR.le _)
  calc
    _ ≤ (n : ℝ) ^ (bookPageSize (μ₀ + 2 * a.ε) (bookSpineSize a.ε a.r n)) := hramsey
    _ ≤ (a.ε * (p - a.ε) / (n : ℝ) ^ 3) *
        (1 + a.ε) ^ (n + (ℓ - 1)) := hpow
    _ ≤ (a.ε * (p - a.ε) / (n : ℝ) ^ 3) *
        (bookMinimumLeftSize a.ε ℓ n : ℝ) :=
      mul_le_mul_of_nonneg_left hfloor hcoeff
    _ = (a.ε / (n : ℝ) ^ 3) * (p - a.ε) *
        (bookMinimumLeftSize a.ε ℓ n : ℝ) := by ring

private theorem concrete_localDichotomy
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hμ₀ : 0 < μ₀) (hx₀ : 0 < x₀) (hp1 : p < 1)
    {L ℓ : ℕ}
    (hschedule : BookAsymptoticScaleBounds a.ε (μ₀ + 2 * a.ε) p a.r L)
    (hLprev : L ≤ ℓ - 1)
    (hlarge : (1 + a.ε) / a.ε ≤ (1 + a.ε) ^ ℓ) :
    concreteBookLocalDichotomy (concreteBookInductionData a ℓ) := by
  intro n NX NR NB α αR αB hn hNX hα hNR hNB hcards hblue hmoment
  have hnpos : 0 < n := by omega
  have hfloor := exponential_le_floor a.ε_pos hlarge (n := n)
  have hsize0 := hschedule.alpha_error n (ℓ - 1) hnpos hLprev
  have hsize :
      (n : ℝ) ^ 2 ≤ a.ε ^ 2 * (bookMinimumLeftSize a.ε ℓ n : ℝ) := by
    exact hsize0.trans
      (mul_le_mul_of_nonneg_left hfloor (sq_nonneg a.ε))
  exact bookLocalDichotomy_of_slack a.two_le_r hn a.ε_pos hμ₀ hx₀ hp1
    a.sum_lt_one a.blue_cutoff a.two_epsilon_lt a.root_gap a.final_slack
    hsize hNX hα hNR hNB hcards hblue hmoment

private theorem exists_bookRightRamseyScale_cutoff
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ∃ N : ℕ, ∀ {ℓ : ℕ}, 0 < ℓ → N ≤ ℓ → ∀ k, 0 < k →
      (ramseyNumber k ℓ : ℝ) ≤
        bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ k := by
  have hregion0 := asymptoticRegionInterior_subset_asymptoticRegion0 a.region
  have hregion2 :
      (x₀ + 2 * a.ε, y₀ + 2 * a.ε) ∈ asymptoticRegion0 :=
    asymptoticRegion0_lower hregion0
      (by linarith [hx₀, a.ε_pos]) (by linarith [a.ε_pos])
      (by linarith [hy₀, a.ε_pos]) (by linarith [a.ε_pos])
  rcases hregion2 with ⟨_, _, N, hN⟩
  refine ⟨N, ?_⟩
  intro ℓ hℓ hNℓ k hk
  have hx : x₀ + a.ε + a.ε = x₀ + 2 * a.ε := by ring
  have hy : y₀ + a.ε + a.ε = y₀ + 2 * a.ε := by ring
  simpa [bookRightRamseyScale, hx, hy] using hN k ℓ hk hℓ (by omega)

private theorem exists_floorMargin_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {ℓ : ℕ}, N ≤ ℓ →
      (1 + ε) / ε ≤ (1 + ε) ^ ℓ := by
  have htend : Tendsto (fun n : ℕ ↦ (1 + ε) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  have hevent : ∀ᶠ n : ℕ in atTop, (1 + ε) / ε ≤ (1 + ε) ^ n :=
    (tendsto_atTop.1 htend) ((1 + ε) / ε)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  exact ⟨N, fun hNℓ ↦ hN _ hNℓ⟩

/-- Concrete realization of every abstract core scale field.  The final
`local_dichotomy` is supplied by the separately checked capped-profile theorem. -/
theorem concreteBookInductionBounds
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    {L ℓ : ℕ}
    (hschedule : BookAsymptoticScaleBounds a.ε (μ₀ + 2 * a.ε) p a.r L)
    (hLprev : L ≤ ℓ - 1)
    (hlarge : (1 + a.ε) / a.ε ≤ (1 + a.ε) ^ ℓ)
    (hright : ∀ k, 0 < k →
      (ramseyNumber k ℓ : ℝ) ≤
        bookRightRamseyScale (x₀ + a.ε) (y₀ + a.ε) a.ε ℓ k) :
    BookInductionBounds (concreteBookInductionData a ℓ) := by
  have hL : L ≤ ℓ := hLprev.trans (Nat.sub_le ℓ 1)
  have hrpos : 0 < a.r :=
    lt_of_lt_of_le (by decide : 0 < 2) a.two_le_r
  have hx : 0 < x₀ + a.ε := add_pos hx₀.1 a.ε_pos
  have hy : 0 < y₀ + a.ε := add_pos hy₀.1 a.ε_pos
  have hμ : 0 < μ₀ + a.ε := add_pos hμ₀.1 a.ε_pos
  have hfloor : 0 < p - a.ε := by linarith [a.two_epsilon_lt, a.ε_pos]
  have hhigh : 0 < μ₀ + 2 * a.ε := by linarith [hμ₀.1, a.ε_pos]
  have hhigh1 : μ₀ + 2 * a.ε < 1 := by
    linarith [a.sum_lt_one, hx₀.1]
  refine {
    exponent_pos := ?_
    x_pos := ?_
    y_pos := ?_
    μ_pos := ?_
    densityFloor_pos := ?_
    highBlueRate_pos := ?_
    highBlueRate_lt_one := ?_
    q_floor := ?_
    q_le_one := ?_
    averagingLoss_nonneg := ?_
    averagingLoss_lt_floor := ?_
    localGap_pos := ?_
    blueBookGap_nonneg := ?_
    local_density_gain := ?_
    spine_pos := ?_
    pageClique_pos := ?_
    blueBook_scale := ?_
    minLeft_blueBook := ?_
    right_ramsey := ?_
    left_large := ?_
    small_high_blue := ?_
    blueBook_q_gain := ?_
    blueBook_moment_gain := ?_
    local_dichotomy := ?_
  }
  · simpa [concreteBookInductionData] using hrpos
  · simpa [concreteBookInductionData] using hx
  · simpa [concreteBookInductionData] using hy
  · simpa [concreteBookInductionData] using hμ
  · simpa [concreteBookInductionData] using hfloor
  · simpa [concreteBookInductionData] using hhigh
  · simpa [concreteBookInductionData] using hhigh1
  · intro n hn
    simp only [concreteBookInductionData]
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [sub_le_sub_iff_left]
    rw [div_le_iff₀ hnR]
    nlinarith [mul_nonneg a.ε_pos.le (sub_nonneg.mpr hn1)]
  · intro n hn
    simp only [concreteBookInductionData]
    have hnR : (0 : ℝ) ≤ n := by positivity
    have hdiv : 0 ≤ a.ε / (n : ℝ) := div_nonneg a.ε_pos.le hnR
    linarith [hp.2]
  · intro n
    simp only [concreteBookInductionData]
    exact div_nonneg a.ε_pos.le (pow_nonneg (by positivity) _)
  · intro n hn
    simp only [concreteBookInductionData]
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
      exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ n))
    have hdiv : a.ε / (n : ℝ) ^ 3 ≤ a.ε := by
      rw [div_le_iff₀ (pow_pos hnR _)]
      nlinarith [mul_nonneg a.ε_pos.le (sub_nonneg.mpr hn1)]
    linarith [a.two_epsilon_lt]
  · intro n hn
    simp only [concreteBookInductionData]
    exact div_pos a.ε_pos (pow_pos (by exact_mod_cast (by omega : 0 < n)) _)
  · intro n hn
    simp only [concreteBookInductionData]
    exact div_nonneg a.ε_pos.le (pow_nonneg (by positivity) _)
  · intro n hn
    simp only [concreteBookInductionData]
    convert density_gain a.ε_pos (show 2 ≤ n by omega) using 1
    all_goals ring
  · intro n hn
    simpa [concreteBookInductionData] using hschedule.spine_pos n (by omega)
  · intro n hn
    simpa [concreteBookInductionData] using hschedule.page_pos n (by omega)
  · intro n hn
    simpa [concreteBookInductionData] using hschedule.page_scale n
  · intro n hn
    simp only [concreteBookInductionData, bookMinimumLeftSize]
    apply Nat.le_floor
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      hschedule.five_page_sq n ℓ (by omega) hL
  · intro k hk
    simpa [concreteBookInductionData] using hright k hk
  · intro n k t NX NY d hn hk ht hNX hNY hdlow hdhigh hmoment hY
    simpa [concreteBookInductionData] using
      concrete_left_large a hμ₀ hx₀ hy₀ hn hk ht hNX hNY hdlow hdhigh hmoment hY
  · intro n k t hn hk ht
    simpa [concreteBookInductionData] using
      concrete_small_high_blue a hschedule hLprev hlarge hn hk ht
  · intro n hn hb
    simp only [concreteBookInductionData]
    convert blue_q_gain a.ε_pos (by omega)
      (hschedule.spine_pos n (by omega)) hb using 1
    all_goals ring
  · intro n k t hn hk ht hb
    simpa [concreteBookInductionData] using
      concrete_blue_moment_gain a hμ₀.1 hx₀.1 hy₀.1 hn hschedule hb
  · change concreteBookLocalDichotomy (concreteBookInductionData a ℓ)
    exact concrete_localDichotomy a hμ₀.1 hx₀.1 hp.2 hschedule hLprev hlarge

/-- One graph-independent cutoff supplies concrete abstract induction bounds
for every later right target `ℓ`. -/
theorem exists_concreteBookInductionBounds
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    {L : ℕ}
    (hschedule : BookAsymptoticScaleBounds a.ε (μ₀ + 2 * a.ε) p a.r L) :
    ∃ L₀ : ℕ, ∀ {ℓ : ℕ}, L₀ ≤ ℓ →
      BookInductionBounds (concreteBookInductionData a ℓ) := by
  obtain ⟨Lright, hright⟩ := exists_bookRightRamseyScale_cutoff a hx₀.1 hy₀.1
  obtain ⟨Lfloor, hfloor⟩ := exists_floorMargin_cutoff a.ε_pos
  let L₀ := max (L + 1) (max Lright Lfloor)
  refine ⟨L₀, ?_⟩
  intro ℓ hL₀
  have hLsucc : L + 1 ≤ ℓ := (le_max_left _ _).trans hL₀
  have hLprev : L ≤ ℓ - 1 := by omega
  have hℓpos : 0 < ℓ := by omega
  have hLright : Lright ≤ ℓ :=
    (le_trans (le_max_left _ _) (le_max_right (L + 1) _)).trans hL₀
  have hLfloor : Lfloor ≤ ℓ :=
    (le_trans (le_max_right _ _) (le_max_right (L + 1) _)).trans hL₀
  exact concreteBookInductionBounds a hμ₀ hx₀ hy₀ hp hschedule hLprev
    (hfloor hLfloor) (hright hℓpos hLright)

/-! ## The book-induction theorem -/

/-- One shifted inverse base, together with its `1 + ε` gain, is bounded by
the corresponding public inverse base. -/
private theorem scaled_inv_le_inv {z ε : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    (1 + ε) * (z + ε)⁻¹ ≤ z⁻¹ := by
  rw [show (1 + ε) * (z + ε)⁻¹ = (1 + ε) / (z + ε) by
      rw [div_eq_mul_inv],
    show z⁻¹ = 1 / z by rw [one_div]]
  rw [div_le_div_iff₀ (add_pos hz.1 hε) hz.1]
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hz.2.le)]

/-- Simultaneously scaling the three shifted bases pays for the exponential
factor in the initial analytic gain. -/
private theorem scaled_bookTarget_le
    {μ₀ x₀ y₀ ε : ℝ} {k ℓ t : ℕ}
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    (1 + ε) ^ (k + t + ℓ) *
        bookTarget (x₀ + ε) (y₀ + ε) (μ₀ + ε) ℓ k t ≤
      (x₀⁻¹) ^ k * (y₀⁻¹) ^ ℓ * (μ₀⁻¹) ^ t := by
  have hx := scaled_inv_le_inv hx₀ hε
  have hy := scaled_inv_le_inv hy₀ hε
  have hμ := scaled_inv_le_inv hμ₀ hε
  have hxshift : 0 < x₀ + ε := add_pos hx₀.1 hε
  have hyshift : 0 < y₀ + ε := add_pos hy₀.1 hε
  have hμshift : 0 < μ₀ + ε := add_pos hμ₀.1 hε
  have hscale0 : 0 ≤ 1 + ε := by linarith
  have hxpow :
      (1 + ε) ^ k * ((x₀ + ε)⁻¹) ^ k ≤ (x₀⁻¹) ^ k := by
    simpa [mul_pow] using
      (pow_le_pow_left₀ (mul_nonneg hscale0 (inv_nonneg.mpr hxshift.le)) hx k)
  have hypow :
      (1 + ε) ^ ℓ * ((y₀ + ε)⁻¹) ^ ℓ ≤ (y₀⁻¹) ^ ℓ := by
    simpa [mul_pow] using
      (pow_le_pow_left₀ (mul_nonneg hscale0 (inv_nonneg.mpr hyshift.le)) hy ℓ)
  have hμpow :
      (1 + ε) ^ t * ((μ₀ + ε)⁻¹) ^ t ≤ (μ₀⁻¹) ^ t := by
    simpa [mul_pow] using
      (pow_le_pow_left₀ (mul_nonneg hscale0 (inv_nonneg.mpr hμshift.le)) hμ t)
  rw [bookTarget]
  calc
    (1 + ε) ^ (k + t + ℓ) *
        (((x₀ + ε)⁻¹) ^ k * ((y₀ + ε)⁻¹) ^ ℓ * ((μ₀ + ε)⁻¹) ^ t) =
        ((1 + ε) ^ k * ((x₀ + ε)⁻¹) ^ k) *
          ((1 + ε) ^ ℓ * ((y₀ + ε)⁻¹) ^ ℓ) *
            ((1 + ε) ^ t * ((μ₀ + ε)⁻¹) ^ t) := by
      rw [pow_add, pow_add]
      ring
    _ ≤ (x₀⁻¹) ^ k * (y₀⁻¹) ^ ℓ * (μ₀⁻¹) ^ t := by
      have hxy := mul_le_mul hxpow hypow
        (mul_nonneg (pow_nonneg hscale0 _)
          (pow_nonneg (inv_nonneg.mpr hyshift.le) _))
        (pow_nonneg (inv_nonneg.mpr hx₀.1.le) _)
      exact mul_le_mul hxy hμpow
        (mul_nonneg (pow_nonneg hscale0 _)
          (pow_nonneg (inv_nonneg.mpr hμshift.le) _))
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr hx₀.1.le) _)
          (pow_nonneg (inv_nonneg.mpr hy₀.1.le) _))

/-- The public product lower bound initializes the concrete strengthened
moment invariant. -/
private theorem initial_bookAdmissible
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {μ₀ x₀ y₀ p : ℝ} (a : BookSlack μ₀ x₀ y₀ p)
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1)
    {L k ℓ t : ℕ}
    (hschedule : BookAsymptoticScaleBounds
      a.ε (μ₀ + 2 * a.ε) p a.r L)
    (hLℓ : L ≤ ℓ) (hk : 0 < k) (ht : 0 < t)
    {A B : Finset W} (hC : Candidate H A B)
    (hd : p ≤ redDensity H A B)
    (hcard : (x₀⁻¹) ^ k * (y₀⁻¹) ^ ℓ * (μ₀⁻¹) ^ t ≤
      (#A : ℝ) * (#B : ℝ)) :
    BookAdmissible (concreteBookInductionData a ℓ).q
      (concreteBookInductionData a ℓ).x
      (concreteBookInductionData a ℓ).y
      (concreteBookInductionData a ℓ).μ
      (concreteBookInductionData a ℓ).exponent ℓ k t H A B := by
  have hn : 0 < k + t := by omega
  have hnR : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by exact_mod_cast hn
  have hdelta0 : 0 ≤ a.ε / ((k + t : ℕ) : ℝ) :=
    div_nonneg a.ε_pos.le hnR.le
  have hq : p - a.ε / ((k + t : ℕ) : ℝ) ≤ redDensity H A B := by
    linarith
  have hscaled := scaled_bookTarget_le (k := k) (ℓ := ℓ) (t := t)
    hμ₀ hx₀ hy₀ a.ε_pos
  have hscaledCard :
      (1 + a.ε) ^ (k + t + ℓ) *
          bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t ≤
        (#A : ℝ) * (#B : ℝ) := hscaled.trans hcard
  have hgain := hschedule.initial_moment_gain a.ε_pos hn hLℓ
  have hxshift : 0 < x₀ + a.ε := add_pos hx₀.1 a.ε_pos
  have hyshift : 0 < y₀ + a.ε := add_pos hy₀.1 a.ε_pos
  have hμshift : 0 < μ₀ + a.ε := add_pos hμ₀.1 a.ε_pos
  have htarget0 : 0 ≤
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t := by
    unfold bookTarget
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hxshift.le) _)
        (pow_nonneg (inv_nonneg.mpr hyshift.le) _))
      (pow_nonneg (inv_nonneg.mpr hμshift.le) _)
  have hdeltaPow0 : 0 ≤ (a.ε / ((k + t : ℕ) : ℝ)) ^ a.r := by positivity
  have htargetDelta :
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t ≤
        (a.ε / ((k + t : ℕ) : ℝ)) ^ a.r *
          ((#A : ℝ) * (#B : ℝ)) := by
    calc
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t =
          1 * bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t := by ring
      _ ≤ ((a.ε / ((k + t : ℕ) : ℝ)) ^ a.r *
            (1 + a.ε) ^ (k + t + ℓ)) *
          bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t := by
        exact mul_le_mul_of_nonneg_right hgain htarget0
      _ = (a.ε / ((k + t : ℕ) : ℝ)) ^ a.r *
          ((1 + a.ε) ^ (k + t + ℓ) *
            bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t) := by ring
      _ ≤ (a.ε / ((k + t : ℕ) : ℝ)) ^ a.r *
          ((#A : ℝ) * (#B : ℝ)) :=
        mul_le_mul_of_nonneg_left hscaledCard hdeltaPow0
  have hbase :
      a.ε / ((k + t : ℕ) : ℝ) ≤
        redDensity H A B - (p - a.ε / ((k + t : ℕ) : ℝ)) := by
    linarith
  have hmoment :
      bookTarget (x₀ + a.ε) (y₀ + a.ε) (μ₀ + a.ε) ℓ k t ≤
        bookMoment (p - a.ε / ((k + t : ℕ) : ℝ)) a.r H A B := by
    rw [bookMoment]
    calc
      _ ≤ (a.ε / ((k + t : ℕ) : ℝ)) ^ a.r *
          ((#A : ℝ) * (#B : ℝ)) := htargetDelta
      _ ≤ (redDensity H A B - (p - a.ε / ((k + t : ℕ) : ℝ))) ^ a.r *
          ((#A : ℝ) * (#B : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hdelta0 hbase a.r)
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = (redDensity H A B - (p - a.ε / ((k + t : ℕ) : ℝ))) ^ a.r *
          (#A : ℝ) * (#B : ℝ) := by ring
  exact ⟨hC, by simpa [concreteBookInductionData] using hq,
    by simpa [concreteBookInductionData, bookMoment] using hmoment⟩

/-- Paper Theorem `t:bookmain`: a sufficiently large dense candidate is
`(k,ℓ,t)`-good. The sole strengthening over the printed statement is that the
unused hypothesis `p > μ₀` is omitted. -/
theorem Candidate.isGood_of_density_card_product
    {μ₀ x₀ y₀ p : ℝ}
    (hμ₀ : μ₀ ∈ Ioo (0 : ℝ) 1) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hxstrict : x₀ < p ^ (1 / (1 - μ₀)) * (1 - μ₀))
    (hregion : (x₀, y₀) ∈ asymptoticRegionInterior) :
    ∃ L₀ : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      {H : SimpleGraph W} [DecidableRel H.Adj]
      {A B : Finset W} {k ℓ t : ℕ},
      0 < k → 0 < ℓ → 0 < t → L₀ ≤ ℓ →
      Candidate H A B → p ≤ redDensity H A B →
      (x₀⁻¹) ^ k * (y₀⁻¹) ^ ℓ * (μ₀⁻¹) ^ t ≤
        (#A : ℝ) * (#B : ℝ) →
      Candidate.IsGood H A B k ℓ t := by
  classical
  let a : BookSlack μ₀ x₀ y₀ p :=
    Classical.choice (exists_bookSlack hμ₀ hx₀ hy₀ hp hxstrict hregion)
  have hεIoo : a.ε ∈ Ioo (0 : ℝ) 1 :=
    a.epsilon_mem_Ioo hμ₀.1 hx₀.1
  have hhigh : 0 < μ₀ + 2 * a.ε := by linarith [hμ₀.1, a.ε_pos]
  have hεp : a.ε < p := by linarith [a.two_epsilon_lt, a.ε_pos]
  obtain ⟨Lscale, hschedule⟩ :=
    exists_bookAsymptoticScaleBounds hεIoo hhigh hεp
      (lt_of_lt_of_le (by decide : 0 < 2) a.two_le_r)
  obtain ⟨Lbounds, hbounds⟩ :=
    exists_concreteBookInductionBounds a hμ₀ hx₀ hy₀ hp hschedule
  refine ⟨max Lscale Lbounds, ?_⟩
  intro W instF instEq H instAdj A B k ℓ t hk hℓ ht hL hC hd hcard
  have hLscale : Lscale ≤ ℓ := (le_max_left _ _).trans hL
  have hLbounds : Lbounds ≤ ℓ := (le_max_right _ _).trans hL
  have hadm := initial_bookAdmissible a hμ₀ hx₀ hy₀ hschedule hLscale
    hk ht hC hd hcard
  simpa [concreteBookInductionData] using
    isGood_of_bookInductionBounds (hbounds hLbounds) hk ht hadm


end RamseyLean
