import RamseyLean.EasyBound
import RamseyLean.Asymptotics.Uniform
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-!
# The asymptotic Ramsey region

This module formalizes the region `𝓡₀`, its closure `𝓡`, its ambient interior
`𝓡_*`, and the four parts of paper Observation `o:r`.  The printed
two-variable little-`o` hypothesis in part (4) is replaced by the uniform-rate
interface needed by the later frontier argument: one `UniformRamseyExpBound`
and its two supporting-line inequalities.

The auxiliary theorem
`asymptoticRegionInterior_subset_asymptoticRegion0` turns an interior point
back into an actual eventual Ramsey bound, as required by book induction.
-/

set_option autoImplicit false

namespace RamseyLean

open Filter Set Topology

/-- The paper's `𝓡₀`: strict unit-square coordinates which give an eventual
product-form Ramsey bound. -/
def asymptoticRegion0 : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Ioo (0 : ℝ) 1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 ∧
    ∃ N : ℕ, ∀ k ℓ : ℕ, 0 < k → 0 < ℓ → N ≤ k + ℓ →
      (ramseyNumber k ℓ : ℝ) ≤ (q.1⁻¹) ^ k * (q.2⁻¹) ^ ℓ}

/-- The paper's asymptotic Ramsey region `𝓡`, defined as the ambient closure
of `asymptoticRegion0`. -/
def asymptoticRegion : Set (ℝ × ℝ) :=
  closure asymptoticRegion0

/-- The paper's `𝓡_*`, the ambient interior of `asymptoticRegion`. -/
def asymptoticRegionInterior : Set (ℝ × ℝ) :=
  interior asymptoticRegion

/-- Coordinatewise lowering preserves the unclosed region `𝓡₀`. -/
theorem asymptoticRegion0_lower {x y x' y' : ℝ}
    (h : (x, y) ∈ asymptoticRegion0)
    (hx' : 0 < x') (hxx : x' ≤ x) (hy' : 0 < y') (hyy : y' ≤ y) :
    (x', y') ∈ asymptoticRegion0 := by
  rcases h with ⟨hx, hy, N, hN⟩
  refine ⟨⟨hx', hxx.trans_lt hx.2⟩, ⟨hy', hyy.trans_lt hy.2⟩, N, ?_⟩
  intro k ℓ hk hℓ hkℓ
  refine (hN k ℓ hk hℓ hkℓ).trans ?_
  apply mul_le_mul
  · exact pow_le_pow_left₀ (inv_nonneg.mpr hx.1.le)
      ((inv_le_inv₀ hx.1 hx').mpr hxx) k
  · exact pow_le_pow_left₀ (inv_nonneg.mpr hy.1.le)
      ((inv_le_inv₀ hy.1 hy').mpr hyy) ℓ
  · exact pow_nonneg (inv_nonneg.mpr hy.1.le) _
  · exact pow_nonneg (inv_nonneg.mpr hx'.le) _

/-- Every point of `𝓡₀` lies in the closed unit square. -/
theorem asymptoticRegion0_subset_unitSquare :
    asymptoticRegion0 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨x, y⟩ ⟨hx, hy, _⟩
  exact ⟨⟨hx.1.le, hx.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩

/-- Closure does not move `𝓡` outside the closed unit square. -/
theorem asymptoticRegion_subset_unitSquare :
    asymptoticRegion ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rw [asymptoticRegion]
  exact closure_minimal asymptoticRegion0_subset_unitSquare
    (isClosed_Icc.prod isClosed_Icc)

/-- Every interior point has both coordinates strictly between zero and one. -/
theorem asymptoticRegionInterior_subset_openUnitSquare :
    asymptoticRegionInterior ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  have h := interior_mono asymptoticRegion_subset_unitSquare
  rw [asymptoticRegionInterior]
  exact h.trans_eq (by simp only [interior_prod_eq, interior_Icc])

private theorem ratio_pos_le_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < a / b ∧ a / b ≤ 1 := by
  have hb : 0 < b := ha.trans_le hab
  exact ⟨div_pos ha hb, (div_le_one hb).mpr hab⟩

namespace AsymptoticRegion

/-- Paper Observation `o:r(2)`: coordinatewise lowering preserves `𝓡`. -/
theorem lower {x y x' y' : ℝ}
    (h : (x, y) ∈ asymptoticRegion)
    (hx' : 0 < x') (hxx : x' ≤ x) (hy' : 0 < y') (hyy : y' ≤ y) :
    (x', y') ∈ asymptoticRegion := by
  let c : ℝ := x' / x
  let d : ℝ := y' / y
  have hx : 0 < x := hx'.trans_le hxx
  have hy : 0 < y := hy'.trans_le hyy
  have hc := ratio_pos_le_one hx' hxx
  have hd := ratio_pos_le_one hy' hyy
  have hmap : ∀ q ∈ asymptoticRegion0,
      (c * q.1, d * q.2) ∈ asymptoticRegion0 := by
    rintro ⟨a, b⟩ hab
    apply asymptoticRegion0_lower hab
    · exact mul_pos hc.1 hab.1.1
    · exact mul_le_of_le_one_left hab.1.1.le hc.2
    · exact mul_pos hd.1 hab.2.1.1
    · exact mul_le_of_le_one_left hab.2.1.1.le hd.2
  have hcont : Continuous (fun q : ℝ × ℝ => (c * q.1, d * q.2)) :=
    (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)
  have hmapped := map_mem_closure hcont (by simpa [asymptoticRegion] using h) hmap
  simpa [asymptoticRegion, c, d, hx.ne', hy.ne'] using hmapped

end AsymptoticRegion

/-- Paper Observation `o:r(3)`: strictly lowering both positive coordinates
of a point of `𝓡` produces an interior point. -/
theorem lower_mem_asymptoticRegionInterior {x y x' y' : ℝ}
    (h : (x, y) ∈ asymptoticRegion)
    (hx' : 0 < x') (hxx : x' < x) (hy' : 0 < y') (hyy : y' < y) :
    (x', y') ∈ asymptoticRegionInterior := by
  have hsub : Ioo (0 : ℝ) x ×ˢ Ioo (0 : ℝ) y ⊆ asymptoticRegion := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact AsymptoticRegion.lower h ha.1 ha.2.le hb.1 hb.2.le
  exact (interior_maximal hsub (isOpen_Ioo.prod isOpen_Ioo))
    ⟨⟨hx', hxx⟩, ⟨hy', hyy⟩⟩

/-- Every interior point supplies an actual eventual product bound.  This
support lemma is stronger than mere membership in `𝓡` and is used by the book
induction. -/
theorem asymptoticRegionInterior_subset_asymptoticRegion0 :
    asymptoticRegionInterior ⊆ asymptoticRegion0 := by
  rintro ⟨x, y⟩ hxy
  have hunit := asymptoticRegionInterior_subset_openUnitSquare hxy
  let g : ℝ → ℝ × ℝ := fun t => (x + t, y + t)
  have hg : Continuous g :=
    (continuous_const.add continuous_id).prodMk (continuous_const.add continuous_id)
  have hnear : g ⁻¹' asymptoticRegionInterior ∈ 𝓝 (0 : ℝ) := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ asymptoticRegionInterior
    have hg0 : g 0 ∈ interior asymptoticRegion := by
      simpa [g, asymptoticRegionInterior] using hxy
    simpa [asymptoticRegionInterior] using
      hg.continuousAt.eventually_mem (isOpen_interior.mem_nhds hg0)
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  rcases (mem_closure_iff_nhds.mp hzero) _ hnear with ⟨δ, hgδ, hδ⟩
  have hδpos : 0 < δ := hδ
  have hgδregion : g δ ∈ asymptoticRegion := interior_subset hgδ
  have hgδclosure : g δ ∈ closure asymptoticRegion0 := by
    simpa [asymptoticRegion] using hgδregion
  have hopen : Ioi x ×ˢ Ioi y ∈ 𝓝 (g δ) :=
    (isOpen_Ioi.prod isOpen_Ioi).mem_nhds ⟨by simp [g, hδpos], by simp [g, hδpos]⟩
  rcases (mem_closure_iff_nhds.mp hgδclosure) _ hopen with
    ⟨⟨a, b⟩, hab, hab0⟩
  exact asymptoticRegion0_lower hab0 hunit.1.1 hab.1.le hunit.2.1 hab.2.le

private theorem exp_neg_log_mul_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-Real.log x * (n : ℝ)) = (x⁻¹) ^ n := by
  rw [show -Real.log x * (n : ℝ) = (n : ℝ) * (-Real.log x) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hx]

private theorem ratio_mem_Ioc {k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    (ℓ : ℝ) / (k : ℝ) ∈ Ioc (0 : ℝ) 1 := by
  have hk : 0 < k := hℓ.trans_le hℓk
  exact ⟨div_pos (by exact_mod_cast hℓ) (by exact_mod_cast hk),
    (div_le_one (by exact_mod_cast hk)).mpr (by exact_mod_cast hℓk)⟩

private theorem scaled_exp_mem_asymptoticRegion0
    {F : ℝ → ℝ} (w : UniformRamseyExpWitness F) {x y δ : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    (hxy : ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log x - s * Real.log y)
    (hyx : ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log y - s * Real.log x) :
    (x * Real.exp (-δ), y * Real.exp (-δ)) ∈ asymptoticRegion0 := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp (w.error_sublinear.eventually_abs_le hδ)
  have he : 0 < Real.exp (-δ) := Real.exp_pos _
  have he1 : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)
  have hxa : 0 < x * Real.exp (-δ) := mul_pos hx.1 he
  have hya : 0 < y * Real.exp (-δ) := mul_pos hy.1 he
  have hlogx : Real.log (x * Real.exp (-δ)) = Real.log x - δ := by
    rw [Real.log_mul hx.1.ne' he.ne', Real.log_exp]
    ring
  have hlogy : Real.log (y * Real.exp (-δ)) = Real.log y - δ := by
    rw [Real.log_mul hy.1.ne' he.ne', Real.log_exp]
    ring
  refine ⟨⟨hxa, (mul_lt_of_lt_one_right hx.1 he1).trans hx.2⟩,
    ⟨hya, (mul_lt_of_lt_one_right hy.1 he1).trans hy.2⟩, 2 * n, ?_⟩
  intro k ℓ hk hℓ hsum
  rcases le_total ℓ k with hℓk | hkℓ
  · have hnk : n ≤ k := by omega
    have herr : w.error k ≤ δ * (k : ℝ) :=
      (le_abs_self _).trans (hn k hnk)
    have hcancel : ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) = (ℓ : ℝ) := by
      exact div_mul_cancel₀ _ (by exact_mod_cast hk.ne')
    have hrate := mul_le_mul_of_nonneg_right
      (hxy _ (ratio_mem_Ioc hℓ hℓk)) (Nat.cast_nonneg k)
    have hbase :
        (-Real.log x - ((ℓ : ℝ) / (k : ℝ)) * Real.log y) * (k : ℝ) =
          -Real.log x * (k : ℝ) - Real.log y * (ℓ : ℝ) := by
      calc
        _ = -Real.log x * (k : ℝ) -
            Real.log y * (((ℓ : ℝ) / (k : ℝ)) * (k : ℝ)) := by ring
        _ = _ := by rw [hcancel]
    have hexponent :
        F ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) + w.error k ≤
          -Real.log (x * Real.exp (-δ)) * (k : ℝ) +
            -Real.log (y * Real.exp (-δ)) * (ℓ : ℝ) := by
      calc
        _ ≤ (-Real.log x - ((ℓ : ℝ) / (k : ℝ)) * Real.log y) *
              (k : ℝ) + δ * (k : ℝ) := add_le_add hrate herr
        _ ≤ _ := by
          rw [hbase, hlogx, hlogy]
          nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg ℓ)]
    refine (w.bound k ℓ hℓ hℓk).trans ?_
    rw [← exp_neg_log_mul_nat hxa k, ← exp_neg_log_mul_nat hya ℓ,
      ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent
  · have hnℓ : n ≤ ℓ := by omega
    have herr : w.error ℓ ≤ δ * (ℓ : ℝ) :=
      (le_abs_self _).trans (hn ℓ hnℓ)
    have hcancel : ((k : ℝ) / (ℓ : ℝ)) * (ℓ : ℝ) = (k : ℝ) := by
      exact div_mul_cancel₀ _ (by exact_mod_cast hℓ.ne')
    have hrate := mul_le_mul_of_nonneg_right
      (hyx _ (ratio_mem_Ioc hk hkℓ)) (Nat.cast_nonneg ℓ)
    have hbase :
        (-Real.log y - ((k : ℝ) / (ℓ : ℝ)) * Real.log x) * (ℓ : ℝ) =
          -Real.log y * (ℓ : ℝ) - Real.log x * (k : ℝ) := by
      calc
        _ = -Real.log y * (ℓ : ℝ) -
            Real.log x * (((k : ℝ) / (ℓ : ℝ)) * (ℓ : ℝ)) := by ring
        _ = _ := by rw [hcancel]
    have hexponent :
        F ((k : ℝ) / (ℓ : ℝ)) * (ℓ : ℝ) + w.error ℓ ≤
          -Real.log (x * Real.exp (-δ)) * (k : ℝ) +
            -Real.log (y * Real.exp (-δ)) * (ℓ : ℝ) := by
      calc
        _ ≤ (-Real.log y - ((k : ℝ) / (ℓ : ℝ)) * Real.log x) *
              (ℓ : ℝ) + δ * (ℓ : ℝ) := add_le_add hrate herr
        _ ≤ _ := by
          rw [hbase, hlogx, hlogy]
          nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg k)]
    refine (w.bound_of_ge k ℓ hk hkℓ).trans ?_
    rw [← exp_neg_log_mul_nat hxa k, ← exp_neg_log_mul_nat hya ℓ,
      ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent

/-- Paper Observation `o:r(4)`, in the use-oriented uniform-rate form needed
by the frontier argument. -/
theorem mem_asymptoticRegion_of_uniform_bound
    {F : ℝ → ℝ} {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hF : UniformRamseyExpBound F)
    (hxy : ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log x - s * Real.log y)
    (hyx : ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log y - s * Real.log x) :
    (x, y) ∈ asymptoticRegion := by
  rcases hF with ⟨w⟩
  let f : ℝ → ℝ × ℝ := fun δ =>
    (x * Real.exp (-δ), y * Real.exp (-δ))
  have hf : Continuous f :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).prodMk
      (continuous_const.mul (Real.continuous_exp.comp continuous_neg))
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  have hmapped := map_mem_closure hf hzero fun δ hδ =>
    scaled_exp_mem_asymptoticRegion0 w hx hy hδ hxy hyx
  simpa [asymptoticRegion, f] using hmapped

/-- Paper Observation `o:r(1)`: the Erdős--Szekeres curve belongs to `𝓡`,
including its two boundary endpoints. -/
theorem baseline_mem_asymptoticRegion (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (x, 1 - x) ∈ asymptoticRegion := by
  let f : ℝ → ℝ × ℝ := fun t => (t, 1 - t)
  have hf : Continuous f := continuous_id.prodMk (continuous_const.sub continuous_id)
  have hxcl : x ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hx
  apply map_mem_closure hf hxcl
  intro t ht
  have h1t : 0 < 1 - t := sub_pos.mpr ht.2
  refine ⟨ht, ⟨h1t, by linarith [ht.1]⟩, 0, ?_⟩
  intro k ℓ hk hℓ _
  refine (ramseyBound_erdosSzekeres ht.1 ht.2 hk hℓ).trans ?_
  apply mul_le_mul
  · exact pow_le_pow_right₀ ((one_le_inv₀ ht.1).mpr ht.2.le) (Nat.sub_le k 1)
  · exact pow_le_pow_right₀ ((one_le_inv₀ h1t).mpr (by linarith [ht.1]))
      (Nat.sub_le ℓ 1)
  · exact pow_nonneg (inv_nonneg.mpr h1t.le) _
  · exact pow_nonneg (inv_nonneg.mpr ht.1.le) _

end RamseyLean
