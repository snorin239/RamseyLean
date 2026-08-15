import RamseyLean.BookInduction
import RamseyLean.Asymptotics.Uniform
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Descent from a dense coloring

This module starts the descent layer by deriving paper Theorem `t:bookCor`
from the book-induction theorem.  The printed balanced maximum-cut argument is
replaced by the existing deterministic excess cut at a slightly smaller
density.  Its quantitative positive excess gives a constant-fraction lower
bound on the candidate product, and an upward perturbation of the second
asymptotic-region coordinate absorbs that constant loss.
-/

set_option autoImplicit false

namespace RamseyLean

open Filter Set Topology
open scoped Finset Topology

universe u

/-- The usual whole-graph red density, normalized by the number of ordered
pairs of distinct vertices.  The numerator is the degree sum, so this is the
paper's unordered red-edge density by the handshaking identity.  As usual for
division in a field, the value is zero on graphs with fewer than two vertices. -/
noncomputable def redGraphDensity {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  (∑ v : V, (G.degree v : ℝ)) /
    ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))

theorem redGraphDensity_nonneg {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : 0 ≤ redGraphDensity G := by
  unfold redGraphDensity
  apply div_nonneg
  · positivity
  · by_cases hV : Fintype.card V = 0
    · simp [hV]
    · have hVone : 1 ≤ Fintype.card V := Nat.one_le_iff_ne_zero.mpr hV
      exact mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (by exact_mod_cast hVone))

/-- If the whole-graph red density is below `1 - q`, some vertex has blue
degree strictly larger than `q |V| - 1`.  This is the averaging step used in
the sparse branch of the descent induction. -/
theorem exists_compl_degree_gt_of_redGraphDensity_lt
    {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℝ}
    (hdensity : redGraphDensity G < 1 - q) :
    ∃ v : V, q * (Fintype.card V : ℝ) - 1 < (Gᶜ.degree v : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  have hnNat : 0 < Fintype.card V := Fintype.card_pos
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hnNat
  have hq : q < 1 := by
    have hnonneg : 0 ≤ redGraphDensity G := redGraphDensity_nonneg G
    linarith
  by_cases hcard : Fintype.card V = 1
  · let v : V := Classical.choice (inferInstance : Nonempty V)
    have hcompLt : Gᶜ.degree v < Fintype.card V :=
      Finset.card_lt_univ_of_notMem (Gᶜ.notMem_neighborFinset_self v)
    have hcomp : Gᶜ.degree v = 0 := by omega
    refine ⟨v, ?_⟩
    rw [hcomp]
    norm_num [hcard]
    exact hq
  · have htwoNat : 2 ≤ Fintype.card V := by omega
    have hnOne : 1 < n := by dsimp [n]; exact_mod_cast htwoNat
    have hdenom : 0 < n * (n - 1) := mul_pos hn (sub_pos.mpr hnOne)
    by_contra hexists
    push Not at hexists
    have hdegreeReal (v : V) :
        (Gᶜ.degree v : ℝ) = n - 1 - (G.degree v : ℝ) := by
      have hredLt : G.degree v < Fintype.card V :=
        Finset.card_lt_univ_of_notMem (G.notMem_neighborFinset_self v)
      have hredLe : G.degree v ≤ Fintype.card V - 1 := Nat.le_sub_one_of_lt hredLt
      rw [G.degree_compl]
      rw [Nat.cast_sub hredLe,
        Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega))]
      dsimp [n]
      norm_num
    have hdegree (v : V) : (1 - q) * n ≤ (G.degree v : ℝ) := by
      have hblue := hexists v
      rw [hdegreeReal v] at hblue
      dsimp [n] at hblue
      linarith
    have hsum : ∑ v : V, (1 - q) * n ≤ ∑ v : V, (G.degree v : ℝ) :=
      Finset.sum_le_sum fun v _ => hdegree v
    have hsumN : (1 - q) * (n * n) ≤ ∑ v : V, (G.degree v : ℝ) := by
      calc
        (1 - q) * (n * n) = n * ((1 - q) * n) := by ring
        _ ≤ _ := by simpa [n] using hsum
    have hsum' : (1 - q) * (n * (n - 1)) < ∑ v : V, (G.degree v : ℝ) := by
      have hless : (1 - q) * (n * (n - 1)) < (1 - q) * (n * n) := by
        have : 0 < 1 - q := sub_pos.mpr hq
        gcongr
        linarith
      exact hless.trans_le hsumN
    have : 1 - q < redGraphDensity G := by
      apply (lt_div_iff₀ hdenom).2
      simpa [redGraphDensity, n, mul_assoc] using hsum'
    linarith

/-- The order threshold in paper Theorem `t:bookCor`, written as the square
root of its squared product.  For positive `x`, `μ`, and `y`, this is
`x^(-k/2) (μ y)^(-ℓ/2)`. -/
noncomputable def bookCorThreshold (x μ y : ℝ) (k ℓ : ℕ) : ℝ :=
  Real.sqrt ((x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ ℓ)

/-- The exponential rate contributed by fixed book parameters at ratio `r`.
Multiplying this quantity by `k` gives the logarithm of
`bookCorThreshold x μ y k ℓ` when `r = ℓ / k`. -/
noncomputable def denseCaseExponent (x μ y r : ℝ) : ℝ :=
  -(Real.log x + r * Real.log μ + r * Real.log y) / 2

private theorem exists_density_slack
    {μ x p : ℝ} (hμ : μ ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hxstrict : x < p ^ (1 / (1 - μ)) * (1 - μ)) :
    ∃ p₀ : ℝ, p₀ ∈ Ioo (0 : ℝ) p ∧
      x < p₀ ^ (1 / (1 - μ)) * (1 - μ) := by
  let a : ℝ := 1 / (1 - μ)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact one_div_nonneg.mpr (sub_nonneg.mpr hμ.2.le)
  have hf : Continuous (fun q : ℝ => q ^ a * (1 - μ)) :=
    (Real.continuous_rpow_const ha).mul continuous_const
  have hnear : {q : ℝ | x < q ^ a * (1 - μ) ∧ 0 < q} ∈ nhds p := by
    filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hxstrict),
      Ioi_mem_nhds hp.1] with q hq hqpos
    exact ⟨hq, hqpos⟩
  have hpclosure : p ∈ closure (Iio p) := by
    rw [closure_Iio]
    exact mem_Iic.mpr le_rfl
  rcases (mem_closure_iff_nhds.mp hpclosure) _ hnear with ⟨p₀, hp₀, hp₀lt⟩
  exact ⟨p₀, ⟨hp₀.2, hp₀lt⟩, by simpa [a] using hp₀.1⟩

private theorem exists_region_slack
    {x y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (hregion : (x, y) ∈ asymptoticRegionInterior) :
    ∃ y₀ : ℝ, y₀ ∈ Ioo y 1 ∧ (x, y₀) ∈ asymptoticRegionInterior := by
  let g : ℝ → ℝ × ℝ := fun q => (x, q)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  have hnear : {q : ℝ | g q ∈ asymptoticRegionInterior ∧ q < 1} ∈ nhds y := by
    filter_upwards [hg.continuousAt.eventually_mem
        (isOpen_interior.mem_nhds (by simpa [asymptoticRegionInterior, g] using hregion)),
      Iio_mem_nhds hy.2] with q hq hqone
    exact ⟨hq, hqone⟩
  have hyclosure : y ∈ closure (Ioi y) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  rcases (mem_closure_iff_nhds.mp hyclosure) _ hnear with ⟨y₀, hy₀, hylt⟩
  exact ⟨y₀, ⟨hylt, hy₀.2⟩, by simpa [g] using hy₀.1⟩

private theorem bookCorThreshold_sq
    {x μ y : ℝ} (hx : 0 < x) (hμ : 0 < μ) (hy : 0 < y) (k ℓ : ℕ) :
    bookCorThreshold x μ y k ℓ ^ 2 =
      (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ ℓ := by
  rw [bookCorThreshold, Real.sq_sqrt]
  positivity

private theorem exp_neg_log_mul_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-Real.log x * (n : ℝ)) = (x⁻¹) ^ n := by
  rw [show -Real.log x * (n : ℝ) = (n : ℝ) * (-Real.log x) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hx]

private theorem bookCorThreshold_eq_exp_denseCaseExponent
    {x μ y : ℝ} (hx : 0 < x) (hμ : 0 < μ) (hy : 0 < y)
    {k ℓ : ℕ} (hk : 0 < k) :
    bookCorThreshold x μ y k ℓ =
      Real.exp (denseCaseExponent x μ y ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ)) := by
  let A : ℝ := denseCaseExponent x μ y ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hexp : Real.exp A ^ 2 = (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ ℓ := by
    rw [pow_two, ← Real.exp_add, ← exp_neg_log_mul_nat hx k,
      ← exp_neg_log_mul_nat hy ℓ, ← exp_neg_log_mul_nat hμ ℓ,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [A, denseCaseExponent]
    field_simp [hk']
    ring
  have hthresholdSq := bookCorThreshold_sq hx hμ hy k ℓ
  have hthresholdNonneg : 0 ≤ bookCorThreshold x μ y k ℓ := by
    simp [bookCorThreshold]
  have hexpPos : 0 < Real.exp A := Real.exp_pos _
  nlinarith

private theorem exp_mul_le_floor_exp_add_mul
    {A d : ℝ} {k : ℕ} (hA : 0 ≤ A)
    (hfactor : 2 ≤ Real.exp (d * (k : ℝ))) :
    Real.exp (A * (k : ℝ)) ≤
      (⌊Real.exp ((A + d) * (k : ℝ))⌋₊ : ℝ) := by
  have hlow : 1 ≤ Real.exp (A * (k : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hA (Nat.cast_nonneg k)
  have hsplit :
      Real.exp ((A + d) * (k : ℝ)) =
        Real.exp (A * (k : ℝ)) * Real.exp (d * (k : ℝ)) := by
    rw [add_mul, Real.exp_add]
  have hminus :
      Real.exp (A * (k : ℝ)) ≤ Real.exp ((A + d) * (k : ℝ)) - 1 := by
    rw [hsplit]
    nlinarith [Real.exp_pos (A * (k : ℝ)), Real.exp_pos (d * (k : ℝ))]
  exact (hminus.trans_lt (Nat.sub_one_lt_floor _)).le

private theorem le_floor_of_scaled_floor_margin
    {B C q : ℝ} (hqpos : 0 < q) (hqone : q < 1)
    (hscaled : C + 2 ≤ q * B) :
    C ≤ q * (⌊B⌋₊ : ℝ) - 1 := by
  have hfloor : B - 1 < (⌊B⌋₊ : ℝ) := Nat.sub_one_lt_floor B
  have hmul : q * (B - 1) < q * (⌊B⌋₊ : ℝ) :=
    mul_lt_mul_of_pos_left hfloor hqpos
  nlinarith

private theorem ratio_mem_Ioc_descent {k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    (ℓ : ℝ) / (k : ℝ) ∈ Ioc (0 : ℝ) 1 := by
  have hk : 0 < k := hℓ.trans_le hℓk
  exact ⟨div_pos (by exact_mod_cast hℓ) (by exact_mod_cast hk),
    (div_le_one (by exact_mod_cast hk)).2 (by exact_mod_cast hℓk)⟩

/-- A uniform small-ratio form of the weighted Erdős--Szekeres bound.  For
every positive exponential allowance there is a fixed positive ratio below
which that allowance bounds all positive Ramsey parameters, with no
asymptotic cutoff. -/
theorem exists_small_ratio_erdosSzekeres (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
        (ℓ : ℝ) / (k : ℝ) ≤ ρ →
        (ramseyNumber k ℓ : ℝ) ≤ Real.exp (ε * (k : ℝ)) := by
  let x : ℝ := Real.exp (-ε / 2)
  let a : ℝ := 1 - x
  let c : ℝ := -Real.log a
  let ρ : ℝ := min (1 / 2) (ε / (2 * c))
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxone : x < 1 := by
    dsimp [x]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hapos : 0 < a := by dsimp [a]; linarith
  have haone : a < 1 := by dsimp [a]; linarith
  have hcpos : 0 < c := by
    dsimp [c]
    exact neg_pos.mpr (Real.log_neg hapos haone)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hcpos))
  have hρone : ρ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨ρ, ⟨hρpos, hρone⟩, ?_⟩
  intro k ℓ hℓ hℓk hratio
  have hk : 0 < k := hℓ.trans_le hℓk
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlogx : Real.log x = -ε / 2 := by simp [x]
  have hfirst : (x⁻¹) ^ (k - 1) ≤ Real.exp ((ε / 2) * (k : ℝ)) := by
    rw [← exp_neg_log_mul_nat hxpos (k - 1)]
    apply Real.exp_le_exp.mpr
    rw [hlogx]
    have hsub : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    nlinarith
  have hratioMul : (ℓ : ℝ) ≤ ρ * (k : ℝ) :=
    (div_le_iff₀ hkReal).mp hratio
  have hρbound : ρ ≤ ε / (2 * c) := min_le_right _ _
  have hsecondExponent : c * ((ℓ - 1 : ℕ) : ℝ) ≤ (ε / 2) * (k : ℝ) := by
    have hsub : (((ℓ - 1 : ℕ) : ℝ)) ≤ (ℓ : ℝ) := by
      exact_mod_cast Nat.sub_le ℓ 1
    calc
      c * ((ℓ - 1 : ℕ) : ℝ) ≤ c * (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_left hsub hcpos.le
      _ ≤ c * (ρ * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hratioMul hcpos.le
      _ ≤ c * ((ε / (2 * c)) * (k : ℝ)) := by
        gcongr
      _ = (ε / 2) * (k : ℝ) := by field_simp [hcpos.ne']
  have hsecond : (a⁻¹) ^ (ℓ - 1) ≤ Real.exp ((ε / 2) * (k : ℝ)) := by
    rw [← exp_neg_log_mul_nat hapos (ℓ - 1)]
    apply Real.exp_le_exp.mpr
    simpa [c] using hsecondExponent
  calc
    (ramseyNumber k ℓ : ℝ) ≤ (x⁻¹) ^ (k - 1) * (a⁻¹) ^ (ℓ - 1) := by
      simpa [a] using ramseyBound_erdosSzekeres hxpos hxone hk hℓ
    _ ≤ Real.exp ((ε / 2) * (k : ℝ)) *
        Real.exp ((ε / 2) * (k : ℝ)) := by
      exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = Real.exp (ε * (k : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem exists_descent_floor_step
    {F D : ℝ → ℝ} {ε δ ρ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hderiv : ∀ r ∈ Ioc (0 : ℝ) 1, HasDerivAt F (D r) r)
    (hDcont : ContinuousOn D (Ioc (0 : ℝ) 1))
    (hFnonneg : ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ F r) :
    ∃ K : ℕ, ∀ {k ℓ : ℕ}, K ≤ k → 2 ≤ ℓ → ℓ ≤ k →
      ρ * (k : ℝ) ≤ (ℓ : ℝ) →
      2 * δ < D ((ℓ : ℝ) / (k : ℝ)) →
      Real.exp
          ((F (((ℓ - 1 : ℕ) : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) ≤
        Real.exp (-D ((ℓ : ℝ) / (k : ℝ)) + δ) *
            (⌊Real.exp
              ((F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ))⌋₊ : ℝ) - 1 := by
  let S : Set ℝ := Icc (ρ / 2) 1
  have hSsub : S ⊆ Ioc (0 : ℝ) 1 := by
    intro r hr
    exact ⟨(half_pos hρ.1).trans_le hr.1, hr.2⟩
  have hDcompact : ContinuousOn D S := hDcont.mono hSsub
  have hDuniform : UniformContinuousOn D S :=
    isCompact_Icc.uniformContinuousOn_of_continuous hDcompact
  obtain ⟨η, hη, hmodulus⟩ :=
    (Metric.uniformContinuousOn_iff.mp hDuniform) (δ / 2) (by linarith)
  let g : ℝ := Real.exp (δ / 2) - 1
  have hg : 0 < g := by
    dsimp [g]
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
  have hexpTendsto :
      Tendsto (fun k : ℕ => g * Real.exp (ε * (k : ℝ))) atTop atTop := by
    exact (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε)).const_mul_atTop hg
  obtain ⟨Kgrowth, hKgrowth⟩ :
      ∃ Kgrowth : ℕ, ∀ k ≥ Kgrowth, 2 ≤ g * Real.exp (ε * (k : ℝ)) :=
    eventually_atTop.mp (hexpTendsto.eventually_ge_atTop 2)
  obtain ⟨Kinv, hKinv⟩ :
      ∃ Kinv : ℕ, max (1 / η) (2 / ρ) < Kinv := exists_nat_gt _
  refine ⟨max Kgrowth Kinv, ?_⟩
  intro k ℓ hK hℓ hℓk hratioLower hslope
  have hKgrowth' : Kgrowth ≤ k := (le_max_left _ _).trans hK
  have hKinv' : Kinv ≤ k := (le_max_right _ _).trans hK
  have hk : 0 < k := lt_of_lt_of_le (by omega : 0 < ℓ) hℓk
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hKinvReal : (Kinv : ℝ) ≤ (k : ℝ) := by exact_mod_cast hKinv'
  have hmaxlt : max (1 / η) (2 / ρ) < (k : ℝ) := hKinv.trans_le hKinvReal
  have hetaK : 1 / η < (k : ℝ) := (le_max_left _ _).trans_lt hmaxlt
  have hrhoK : 2 / ρ < (k : ℝ) := (le_max_right _ _).trans_lt hmaxlt
  have hinvEta : 1 / (k : ℝ) < η := by
    rw [div_lt_iff₀ hkReal]
    have := (div_lt_iff₀ hη).mp hetaK
    nlinarith
  have hinvRho : 1 / (k : ℝ) < ρ / 2 := by
    rw [div_lt_iff₀ hkReal]
    have := (div_lt_iff₀ hρ.1).mp hrhoK
    nlinarith
  let r : ℝ := (ℓ : ℝ) / (k : ℝ)
  let r₀ : ℝ := ((ℓ - 1 : ℕ) : ℝ) / (k : ℝ)
  have hprevPos : 0 < ℓ - 1 := by omega
  have hprevLe : ℓ - 1 ≤ k := (Nat.sub_le ℓ 1).trans hℓk
  have hrIoc : r ∈ Ioc (0 : ℝ) 1 := by
    simpa [r] using ratio_mem_Ioc_descent (by omega : 0 < ℓ) hℓk
  have hr₀Ioc : r₀ ∈ Ioc (0 : ℝ) 1 := by
    simpa [r₀] using ratio_mem_Ioc_descent hprevPos hprevLe
  have hrLower : ρ ≤ r := by
    dsimp [r]
    exact (le_div_iff₀ hkReal).2 hratioLower
  have hr₀eq : r₀ = r - 1 / (k : ℝ) := by
    dsimp [r₀, r]
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]
    norm_num
    field_simp [hkReal.ne']
  have hr₀Lower : ρ / 2 ≤ r₀ := by
    rw [hr₀eq]
    linarith
  have hrS : r ∈ S := by
    exact ⟨(div_le_self hρ.1.le (by norm_num)).trans hrLower, hrIoc.2⟩
  have hr₀S : r₀ ∈ S := ⟨hr₀Lower, hr₀Ioc.2⟩
  have hr₀r : r₀ < r := by
    rw [hr₀eq]
    exact sub_lt_self _ (div_pos zero_lt_one hkReal)
  have hintervalSub : Icc r₀ r ⊆ Ioc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨hr₀Ioc.1.trans_le hz.1, hz.2.trans hrIoc.2⟩
  have hFcontinuous : ContinuousOn F (Icc r₀ r) := by
    intro z hz
    exact (hderiv z (hintervalSub hz)).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hzslope⟩ := exists_hasDerivAt_eq_slope
    (f := F) (f' := D) hr₀r hFcontinuous
    (fun z hz => hderiv z (hintervalSub ⟨hz.1.le, hz.2.le⟩))
  have hwidth : r - r₀ = 1 / (k : ℝ) := by rw [hr₀eq]; ring
  have hzslope' : D z = (F r - F r₀) * (k : ℝ) := by
    rw [hwidth] at hzslope
    calc
      D z = (F r - F r₀) / (1 / (k : ℝ)) := hzslope
      _ = (F r - F r₀) * (k : ℝ) := by field_simp [hkReal.ne']
  have hmean : F r * (k : ℝ) - D z = F r₀ * (k : ℝ) := by
    rw [hzslope']
    ring
  have hzS : z ∈ S :=
    ⟨hr₀Lower.trans hz.1.le, hz.2.le.trans hrIoc.2⟩
  have hdist : dist r z < η := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hz.2.le)]
    calc
      r - z < r - r₀ := sub_lt_sub_left hz.1 r
      _ = 1 / (k : ℝ) := hwidth
      _ < η := hinvEta
  have hDdist := hmodulus r hrS z hzS hdist
  have hDdiff : D r - D z < δ / 2 := by
    exact (le_abs_self (D r - D z)).trans_lt (by simpa [Real.dist_eq] using hDdist)
  let E : ℝ := Real.exp ((F r + ε) * (k : ℝ))
  let E₀ : ℝ := Real.exp ((F r₀ + ε) * (k : ℝ))
  let q : ℝ := Real.exp (-D r + δ)
  have hscaled : Real.exp (δ / 2) * E₀ < q * E := by
    dsimp [E₀, q, E]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    nlinarith [hmean, hDdiff]
  have hbase : Real.exp (ε * (k : ℝ)) ≤ E₀ := by
    dsimp [E₀]
    apply Real.exp_le_exp.mpr
    have hF₀ := hFnonneg r₀ hr₀Ioc
    nlinarith [mul_nonneg hF₀ (Nat.cast_nonneg k)]
  have hgrowth : 2 ≤ g * Real.exp (ε * (k : ℝ)) :=
    hKgrowth k hKgrowth'
  have hmarginFactor : 2 ≤ g * E₀ :=
    hgrowth.trans (mul_le_mul_of_nonneg_left hbase hg.le)
  have hmargin : E₀ + 2 ≤ Real.exp (δ / 2) * E₀ := by
    dsimp [g] at hmarginFactor
    nlinarith
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqone : q < 1 := by
    dsimp [q]
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hfloor := le_floor_of_scaled_floor_margin hqpos hqone
    (hmargin.trans hscaled.le)
  simpa [E₀, q, E, r₀, r] using hfloor

/-- Paper Theorem `t:bookCor`: every sufficiently large red-blue coloring
whose whole-graph red density is at least `p` contains a red `K_k` or a blue
`K_ℓ`.  The real order threshold is the printed
`x^(-k/2) (μ y)^(-ℓ/2)`, exposed as `bookCorThreshold`.

The proof uses a quantitative excess cut at a nearby density `p₀ < p`
instead of the paper's balanced maximum-density cut; this changes no theorem
hypothesis or conclusion. -/
theorem ramseyBound_of_redDensity
    {μ x y p : ℝ}
    (hμ : μ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hxstrict : x < p ^ (1 / (1 - μ)) * (1 - μ))
    (hregion : (x, y) ∈ asymptoticRegionInterior) :
    ∃ L₀ : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      {G : SimpleGraph W} [DecidableRel G.Adj] {k ℓ : ℕ},
      0 < k → 0 < ℓ → L₀ ≤ ℓ →
      bookCorThreshold x μ y k ℓ ≤ Fintype.card W →
      p ≤ redGraphDensity G →
      hasRedClique G Finset.univ k ∨ hasBlueClique G Finset.univ ℓ := by
  classical
  obtain ⟨p₀, hp₀, hxstrict₀⟩ := exists_density_slack hμ hp hxstrict
  obtain ⟨y₀, hy₀, hregion₀⟩ := exists_region_slack hy hregion
  have hp₀unit : p₀ ∈ Ioo (0 : ℝ) 1 := ⟨hp₀.1, hp₀.2.trans hp.2⟩
  have hy₀unit : y₀ ∈ Ioo (0 : ℝ) 1 := ⟨hy.1.trans hy₀.1, hy₀.2⟩
  obtain ⟨Lbook, hbook⟩ :=
    Candidate.isGood_of_density_card_product hμ hx hy₀unit hp₀unit hxstrict₀ hregion₀
  let δ : ℝ := p - p₀
  have hδ : 0 < δ := sub_pos.mpr hp₀.2
  have hratio : 1 < y₀ / y := (one_lt_div hy.1).mpr hy₀.1
  obtain ⟨Lratio, hLratio⟩ : ∃ Lratio : ℕ, ∀ ℓ ≥ Lratio,
      8 / δ ≤ (y₀ / y) ^ ℓ :=
    eventually_atTop.mp
      ((tendsto_pow_atTop_atTop_of_one_lt hratio).eventually_ge_atTop (8 / δ))
  have hyinv : 1 < y⁻¹ := (one_lt_inv₀ hy.1).mpr hy.2
  obtain ⟨Lsize, hLsize⟩ : ∃ Lsize : ℕ, ∀ ℓ ≥ Lsize,
      4 ≤ (y⁻¹) ^ ℓ :=
    eventually_atTop.mp
      ((tendsto_pow_atTop_atTop_of_one_lt hyinv).eventually_ge_atTop 4)
  refine ⟨max Lbook (max Lratio Lsize), ?_⟩
  intro W instF instEq G instAdj k ℓ hk hℓ hL horder hdensity
  have hLbook : Lbook ≤ ℓ := (le_max_left _ _).trans hL
  have hLratio' : Lratio ≤ ℓ :=
    (le_max_left Lratio Lsize).trans ((le_max_right Lbook _).trans hL)
  have hLsize' : Lsize ≤ ℓ :=
    (le_max_right Lratio Lsize).trans ((le_max_right Lbook _).trans hL)
  let n : ℝ := Fintype.card W
  let P : ℝ := (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ ℓ
  let P₀ : ℝ := (x⁻¹) ^ k * (y₀⁻¹) ^ ℓ * (μ⁻¹) ^ ℓ
  have hxinv : 1 ≤ x⁻¹ := ((one_lt_inv₀ hx.1).mpr hx.2).le
  have hμinv : 1 ≤ μ⁻¹ := ((one_lt_inv₀ hμ.1).mpr hμ.2).le
  have hPnonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hP₀pos : 0 < P₀ := by
    dsimp [P₀]
    exact mul_pos
      (mul_pos (pow_pos (inv_pos.mpr hx.1) _) (pow_pos (inv_pos.mpr hy₀unit.1) _))
      (pow_pos (inv_pos.mpr hμ.1) _)
  have hPfour : 4 ≤ P := by
    calc
      4 ≤ (y⁻¹) ^ ℓ := hLsize ℓ hLsize'
      _ = 1 * (y⁻¹) ^ ℓ * 1 := by ring
      _ ≤ (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ ℓ := by
        gcongr
        · exact one_le_pow₀ hxinv
        · exact one_le_pow₀ hμinv
      _ = P := rfl
  have hthresholdTwo : (2 : ℝ) ≤ bookCorThreshold x μ y k ℓ := by
    apply (Real.le_sqrt (by norm_num) hPnonneg).mpr
    norm_num [P] at hPfour ⊢
    exact hPfour
  have hnTwoReal : (2 : ℝ) ≤ n := hthresholdTwo.trans (by simpa [n] using horder)
  have hnTwo : 2 ≤ Fintype.card W := by
    have hnTwoReal' : (2 : ℝ) ≤ (Fintype.card W : ℝ) := by simpa [n] using hnTwoReal
    exact_mod_cast hnTwoReal'
  have hdenom : 0 < n * (n - 1) := by
    have hnpos : 0 < n := by linarith
    have hnminus : 0 < n - 1 := by linarith
    exact mul_pos hnpos hnminus
  have hdegree : p * (n * (n - 1)) ≤ ∑ v : W, (G.degree v : ℝ) := by
    apply (le_div_iff₀ hdenom).mp
    simpa [redGraphDensity, n, mul_assoc] using hdensity
  have hPsq : P ≤ n ^ 2 := by
    have hsqrtSq : bookCorThreshold x μ y k ℓ ^ 2 = P := by
      simpa [P] using bookCorThreshold_sq hx.1 hμ.1 hy.1 k ℓ
    have hsqrtNonneg : 0 ≤ bookCorThreshold x μ y k ℓ := by
      simp [bookCorThreshold]
    have hnNonneg : 0 ≤ n := by positivity
    nlinarith
  have hyfactor : (y⁻¹) ^ ℓ = (y₀ / y) ^ ℓ * (y₀⁻¹) ^ ℓ := by
    rw [← mul_pow]
    congr 1
    field_simp [hy.1.ne', (hy.1.trans hy₀.1).ne']
  have hPratio : P = (y₀ / y) ^ ℓ * P₀ := by
    dsimp [P, P₀]
    rw [hyfactor]
    ring
  have hEight : 8 * P₀ ≤ δ * P := by
    rw [hPratio]
    calc
      8 * P₀ = δ * (8 / δ) * P₀ := by field_simp [hδ.ne']
      _ ≤ δ * (y₀ / y) ^ ℓ * P₀ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hLratio ℓ hLratio') hδ.le) hP₀pos.le
      _ = δ * ((y₀ / y) ^ ℓ * P₀) := by ring
  have hnSq : n ^ 2 ≤ 2 * (n * (n - 1)) := by nlinarith
  have hP₀scale : P₀ ≤ δ * (n * (n - 1)) / 4 := by
    have hδsq : δ * P ≤ δ * n ^ 2 := mul_le_mul_of_nonneg_left hPsq hδ.le
    have hδn : δ * n ^ 2 ≤ δ * (2 * (n * (n - 1))) :=
      mul_le_mul_of_nonneg_left hnSq hδ.le
    nlinarith
  obtain ⟨X, Y, hXY, _hunion, hcut⟩ := exists_bipartition_excess_ge G p₀
  have hcutLower : δ * (n * (n - 1)) / 4 ≤ excess G p₀ X Y := by
    calc
      δ * (n * (n - 1)) / 4 ≤
          ((∑ v : W, (G.degree v : ℝ)) - p₀ * n * (n - 1)) / 4 := by
        dsimp [δ]
        nlinarith
      _ ≤ excess G p₀ X Y := by simpa [n, mul_assoc] using hcut
  have hP₀excess : P₀ ≤ excess G p₀ X Y := hP₀scale.trans hcutLower
  have hexcessPos : 0 < excess G p₀ X Y := hP₀pos.trans_le hP₀excess
  have hC : Candidate G X Y := Candidate.of_disjoint_of_excess_pos hXY hexcessPos
  have hdense₀ : p₀ ≤ redDensity G X Y := by
    have hprodPos : 0 < (#X : ℝ) * (#Y : ℝ) := by
      exact mul_pos (by exact_mod_cast hC.left_card_pos) (by exact_mod_cast hC.right_card_pos)
    rw [hC.excess_eq_density_sub_mul p₀] at hexcessPos
    rcases (mul_pos_iff.mp hexcessPos) with hpos | hneg
    · exact (sub_pos.mp hpos.1).le
    · exact False.elim ((not_lt_of_ge hprodPos.le) hneg.2)
  have hexcessLe : excess G p₀ X Y ≤ (#X : ℝ) * (#Y : ℝ) := by
    have hred : (redInteredgeCount G X Y : ℝ) ≤ (#X : ℝ) * (#Y : ℝ) := by
      exact_mod_cast redInteredgeCount_le_mul (G := G) X Y
    rw [excess]
    calc
      (redInteredgeCount G X Y : ℝ) - p₀ * (#X : ℝ) * (#Y : ℝ) ≤
          redInteredgeCount G X Y := by
        exact sub_le_self _ (mul_nonneg (mul_nonneg hp₀.1.le (Nat.cast_nonneg _))
          (Nat.cast_nonneg _))
      _ ≤ (#X : ℝ) * (#Y : ℝ) := hred
  have hcard : P₀ ≤ (#X : ℝ) * (#Y : ℝ) := hP₀excess.trans hexcessLe
  exact (hbook hk hℓ hℓ hLbook hC hdense₀ (by simpa [P₀] using hcard)).to_univ

private structure DenseCaseAnchor
    (F D M : ℝ → ℝ) (ε c : ℝ) where
  δ : ℝ
  x : ℝ
  y : ℝ
  p : ℝ
  L : ℕ
  delta_pos : 0 < δ
  delta_slope : 2 * δ < D c
  x_unit : x ∈ Ioo (0 : ℝ) 1
  mu_unit : M c ∈ Ioo (0 : ℝ) 1
  y_unit : y ∈ Ioo (0 : ℝ) 1
  p_unit : p ∈ Ioo (0 : ℝ) 1
  x_strict : x < p ^ (1 / (1 - M c)) * (1 - M c)
  region : (x, y) ∈ asymptoticRegionInterior
  density_at : p < 1 - Real.exp (-D c + δ)
  rate_at : denseCaseExponent x (M c) y c < F c + ε
  book :
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      {G : SimpleGraph W} [DecidableRel G.Adj] {k ℓ : ℕ},
      0 < k → 0 < ℓ → L ≤ ℓ →
      bookCorThreshold x (M c) y k ℓ ≤ Fintype.card W →
      p ≤ redGraphDensity G →
      hasRedClique G Finset.univ k ∨ hasBlueClique G Finset.univ ℓ

private noncomputable def DenseCaseAnchor.patch
    {F D M : ℝ → ℝ} {ε c : ℝ} (A : DenseCaseAnchor F D M ε c) : Set ℝ :=
  {r | A.p < 1 - Real.exp (-D r + A.δ) ∧
    denseCaseExponent A.x (M c) A.y r < F r + ε ∧
    2 * A.δ < D r}

private theorem exists_denseCaseAnchor
    {F D M X Y : ℝ → ℝ} {ε ρ c : ℝ}
    (hε : 0 < ε) (hc : c ∈ Icc ρ 1)
    (hF : ContinuousWithinAt F (Icc ρ 1) c)
    (hD : ContinuousWithinAt D (Icc ρ 1) c)
    (hDpos : 0 < D c) (hM : M c ∈ Ioo (0 : ℝ) 1)
    (hX : X c ∈ Ioo (0 : ℝ) 1) (hY : Y c ∈ Ioo (0 : ℝ) 1)
    (hXeq : X c =
      (1 - Real.exp (-D c)) ^ (1 / (1 - M c)) * (1 - M c))
    (hregion : (X c, Y c) ∈ asymptoticRegion)
    (hslack : denseCaseExponent (X c) (M c) (Y c) c < F c) :
    ∃ A : DenseCaseAnchor F D M ε c,
      A.patch ∈ 𝓝[Icc ρ 1] c := by
  classical
  let η : ℝ := ε / 4
  let e : ℝ := Real.exp (-η)
  let x : ℝ := X c * e
  let y : ℝ := Y c * e
  have hη : 0 < η := by dsimp [η]; linarith
  have hepos : 0 < e := by dsimp [e]; positivity
  have helt : e < 1 := by
    dsimp [e]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hη)
  have hxx : x < X c := by
    dsimp [x]
    exact mul_lt_of_lt_one_right hX.1 helt
  have hyy : y < Y c := by
    dsimp [y]
    exact mul_lt_of_lt_one_right hY.1 helt
  have hx : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hX.1 hepos, hxx.trans hX.2⟩
  have hy : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hY.1 hepos, hyy.trans hY.2⟩
  have hlogx : Real.log x = Real.log (X c) - η := by
    dsimp [x, e]
    rw [Real.log_mul hX.1.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hlogy : Real.log y = Real.log (Y c) - η := by
    dsimp [y, e]
    rw [Real.log_mul hY.1.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hrateEq :
      denseCaseExponent x (M c) y c =
        denseCaseExponent (X c) (M c) (Y c) c + η * (1 + c) / 2 := by
    simp only [denseCaseExponent, hlogx, hlogy]
    ring
  have hcle : c ≤ 1 := hc.2
  have hinc : η * (1 + c) / 2 ≤ ε / 4 := by
    have hone : 1 + c ≤ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hone hη.le
    dsimp [η] at hmul ⊢
    nlinarith
  have hrate : denseCaseExponent x (M c) y c < F c + ε := by
    rw [hrateEq]
    linarith
  have hregion' : (x, y) ∈ asymptoticRegionInterior :=
    lower_mem_asymptoticRegionInterior hregion hx.1 hxx hy.1 hyy
  let q : ℝ := 1 - Real.exp (-D c)
  have hq : q ∈ Ioo (0 : ℝ) 1 := by
    have hexpPos : 0 < Real.exp (-D c) := Real.exp_pos _
    have hexpOne : Real.exp (-D c) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hDpos)
    dsimp [q]
    constructor <;> linarith
  have hxcritical : x < q ^ (1 / (1 - M c)) * (1 - M c) := by
    calc
      x < X c := hxx
      _ = q ^ (1 / (1 - M c)) * (1 - M c) := by simpa [q] using hXeq
  obtain ⟨p, hp, hxstrict⟩ := exists_density_slack hM hq hxcritical
  have hpunit : p ∈ Ioo (0 : ℝ) 1 := ⟨hp.1, hp.2.trans hq.2⟩
  have hqcont : Continuous (fun d : ℝ => 1 - Real.exp (-D c + d)) := by
    fun_prop
  have htwocont : Continuous (fun d : ℝ => 2 * d) := by fun_prop
  have hdnear :
      {d : ℝ | p < 1 - Real.exp (-D c + d) ∧ 2 * d < D c} ∈ 𝓝 0 := by
    filter_upwards [hqcont.continuousAt.eventually
        (Ioi_mem_nhds (by simpa [q] using hp.2)),
      htwocont.continuousAt.eventually (Iio_mem_nhds (by simpa using hDpos))]
      with d hdensity hslope
    exact ⟨hdensity, hslope⟩
  have hzeroClosure : (0 : ℝ) ∈ closure (Ioi 0) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  rcases (mem_closure_iff_nhds.mp hzeroClosure) _ hdnear with
    ⟨d, hd, hdpos⟩
  obtain ⟨L, hbook⟩ :=
    ramseyBound_of_redDensity hM hx hy hpunit hxstrict hregion'
  let A : DenseCaseAnchor F D M ε c :=
    { δ := d
      x := x
      y := y
      p := p
      L := L
      delta_pos := hdpos
      delta_slope := hd.2
      x_unit := hx
      mu_unit := hM
      y_unit := hy
      p_unit := hpunit
      x_strict := hxstrict
      region := hregion'
      density_at := hd.1
      rate_at := hrate
      book := hbook }
  refine ⟨A, ?_⟩
  have hdensityCont :
      ContinuousWithinAt (fun r : ℝ => 1 - Real.exp (-D r + A.δ))
        (Icc ρ 1) c := by
    exact continuousWithinAt_const.sub (hD.neg.add continuousWithinAt_const).rexp
  have hrateCont : Continuous (fun r : ℝ => denseCaseExponent A.x (M c) A.y r) := by
    unfold denseCaseExponent
    fun_prop
  have hrightCont : ContinuousWithinAt (fun r : ℝ => F r + ε) (Icc ρ 1) c :=
    hF.add continuousWithinAt_const
  filter_upwards [hdensityCont.eventually (Ioi_mem_nhds A.density_at),
    (hrightCont.sub hrateCont.continuousWithinAt).eventually
      (Ioi_mem_nhds (sub_pos.mpr A.rate_at)),
    (hD.sub continuousWithinAt_const).eventually
      (Ioi_mem_nhds (sub_pos.mpr A.delta_slope))] with r hdensity hrate' hslope
  exact ⟨hdensity, sub_pos.mp hrate', sub_pos.mp hslope⟩

/-- Paper Claim `c:gen`: on a compact interval of positive ratios, the dense
case of the descent argument has a single density slack and a single lower
cutoff for `ℓ`.

The formal support statement separates the slope function `D` from its later
interpretation as `F'`, is generalized from `Fin N` to any finite vertex type,
and additionally returns the uniform inequality `2 * δ < D r`.  Its proof
uses finitely many local frozen-parameter patches rather than the paper's
single uniformly perturbed parameter family; consequently only `F` and `D`
need to be continuous on the compact interval. -/
theorem dense_case_uniform
    {F D M X Y : ℝ → ℝ} {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (hF : ContinuousOn F (Icc ρ 1))
    (hD : ContinuousOn D (Icc ρ 1))
    (hDpos : ∀ r ∈ Icc ρ 1, 0 < D r)
    (hM : ∀ r ∈ Icc ρ 1, M r ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ r ∈ Icc ρ 1, X r ∈ Ioo (0 : ℝ) 1)
    (hY : ∀ r ∈ Icc ρ 1, Y r ∈ Ioo (0 : ℝ) 1)
    (hXeq : ∀ r ∈ Icc ρ 1,
      X r = (1 - Real.exp (-D r)) ^ (1 / (1 - M r)) * (1 - M r))
    (hregion : ∀ r ∈ Icc ρ 1, (X r, Y r) ∈ asymptoticRegion)
    (hslack : ∀ r ∈ Icc ρ 1,
      denseCaseExponent (X r) (M r) (Y r) r < F r) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ∈ Icc ρ 1, 2 * δ < D r) ∧
      ∃ L : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {G : SimpleGraph W} [DecidableRel G.Adj] {k ℓ : ℕ},
        0 < k → 0 < ℓ → ℓ ≤ k →
        ρ * (k : ℝ) ≤ (ℓ : ℝ) → L ≤ ℓ →
        Real.exp ((F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) ≤
          (Fintype.card W : ℝ) →
        1 - Real.exp (-D ((ℓ : ℝ) / (k : ℝ)) + δ) ≤ redGraphDensity G →
        hasRedClique G Finset.univ k ∨ hasBlueClique G Finset.univ ℓ := by
  classical
  have hlocal : ∀ c : Icc ρ 1, ∃ A : DenseCaseAnchor F D M ε c.1,
      A.patch ∈ 𝓝[Icc ρ 1] c.1 := by
    intro c
    exact exists_denseCaseAnchor hε c.2 (hF c.1 c.2) (hD c.1 c.2)
      (hDpos c.1 c.2) (hM c.1 c.2) (hX c.1 c.2) (hY c.1 c.2)
      (hXeq c.1 c.2) (hregion c.1 c.2) (hslack c.1 c.2)
  choose A hApatch using hlocal
  obtain ⟨t, htcover⟩ := isCompact_Icc.elim_nhdsWithin_subcover'
    (fun c hc => (A ⟨c, hc⟩).patch)
    (fun c hc => hApatch ⟨c, hc⟩)
  have hρK : ρ ∈ Icc ρ 1 := by exact ⟨le_rfl, hρ.2⟩
  have htne : t.Nonempty := by
    by_contra ht
    have htempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simpa [htempty] using htcover hρK
  let δ : ℝ := t.inf' htne (fun c => (A c).δ)
  let L : ℕ := t.sup (fun c => (A c).L)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact (Finset.lt_inf'_iff htne).2 fun c _ => (A c).delta_pos
  have hδle : ∀ c ∈ t, δ ≤ (A c).δ := by
    intro c hc
    dsimp [δ]
    exact Finset.inf'_le _ hc
  have hLs : ∀ c ∈ t, (A c).L ≤ L := by
    intro c hc
    dsimp [L]
    exact Finset.le_sup (f := fun c => (A c).L) hc
  have hchoose : ∀ r ∈ Icc ρ 1, ∃ c ∈ t, r ∈ (A c).patch := by
    intro r hr
    have hmem := htcover hr
    simp only [Set.mem_iUnion] at hmem
    rcases hmem with ⟨c, hc, hpatch⟩
    refine ⟨c, hc, ?_⟩
    convert hpatch using 1
  have hδslope : ∀ r ∈ Icc ρ 1, 2 * δ < D r := by
    intro r hr
    obtain ⟨c, hc, hrc⟩ := hchoose r hr
    have htwice : 2 * δ ≤ 2 * (A c).δ :=
      mul_le_mul_of_nonneg_left (hδle c hc) (by norm_num)
    exact htwice.trans_lt hrc.2.2
  refine ⟨δ, hδpos, hδslope, L, ?_⟩
  intro W instF instEq G instAdj k ℓ hk hℓ hℓk hratioLower hL horder hdensity
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio : (ℓ : ℝ) / (k : ℝ) ∈ Icc ρ 1 := by
    constructor
    · exact (le_div_iff₀ hkReal).2 hratioLower
    · exact (div_le_one hkReal).2 (by exact_mod_cast hℓk)
  obtain ⟨c, hc, hpatch⟩ :=
    hchoose ((ℓ : ℝ) / (k : ℝ)) hratio
  have hLlocal : (A c).L ≤ ℓ := (hLs c hc).trans hL
  have hthreshold :
      bookCorThreshold (A c).x (M c.1) (A c).y k ℓ ≤ Fintype.card W := by
    calc
      bookCorThreshold (A c).x (M c.1) (A c).y k ℓ =
          Real.exp (denseCaseExponent (A c).x (M c.1) (A c).y
            ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ)) :=
        bookCorThreshold_eq_exp_denseCaseExponent
          (A c).x_unit.1 (A c).mu_unit.1 (A c).y_unit.1 hk
      _ ≤ Real.exp ((F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := by
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hpatch.2.1.le (Nat.cast_nonneg k))
      _ ≤ Fintype.card W := horder
  have hqmono :
      1 - Real.exp (-D ((ℓ : ℝ) / (k : ℝ)) + (A c).δ) ≤
        1 - Real.exp (-D ((ℓ : ℝ) / (k : ℝ)) + δ) := by
    have hexp :
        Real.exp (-D ((ℓ : ℝ) / (k : ℝ)) + δ) ≤
          Real.exp (-D ((ℓ : ℝ) / (k : ℝ)) + (A c).δ) :=
      Real.exp_le_exp.mpr (by linarith [hδle c hc])
    linarith
  have hdensityLocal : (A c).p ≤ redGraphDensity G :=
    hpatch.1.le.trans (hqmono.trans hdensity)
  exact (A c).book hk hℓ hLlocal hthreshold hdensityLocal

/-- Paper Theorem `t:general`: a positive rate function satisfying the descent
conditions gives a uniform exponential Ramsey bound.

The formal statement represents `F'` by an explicit function `D` together
with pointwise `HasDerivAt` proofs and continuity on `(0,1]`.  It retains the
agreed continuity hypothesis on `M`; the frozen-parameter proof of
`dense_case_uniform` is stronger and does not itself need that hypothesis. -/
theorem uniformRamseyExpBound_of_descent
    {F D M X Y : ℝ → ℝ}
    (hderiv : ∀ r ∈ Ioc (0 : ℝ) 1, HasDerivAt F (D r) r)
    (hDcont : ContinuousOn D (Ioc (0 : ℝ) 1))
    (_hMcont : ContinuousOn M (Ioc (0 : ℝ) 1))
    (hFnonneg : ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ F r)
    (hDpos : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < D r)
    (hM : ∀ r ∈ Ioc (0 : ℝ) 1, M r ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ r ∈ Ioc (0 : ℝ) 1, X r ∈ Ioo (0 : ℝ) 1)
    (hY : ∀ r ∈ Ioc (0 : ℝ) 1, Y r ∈ Ioo (0 : ℝ) 1)
    (hXeq : ∀ r ∈ Ioc (0 : ℝ) 1,
      X r = (1 - Real.exp (-D r)) ^ (1 / (1 - M r)) * (1 - M r))
    (hregion : ∀ r ∈ Ioc (0 : ℝ) 1, (X r, Y r) ∈ asymptoticRegion)
    (hslack : ∀ r ∈ Ioc (0 : ℝ) 1,
      denseCaseExponent (X r) (M r) (Y r) r < F r) :
    UniformRamseyExpBound F := by
  classical
  apply uniformRamseyExpBound_of_eventually
  intro ε hε
  obtain ⟨ρ, hρ, hsmall⟩ := exists_small_ratio_erdosSzekeres (ε / 2) (by linarith)
  have hρIoc : ρ ∈ Ioc (0 : ℝ) 1 := ⟨hρ.1, hρ.2.le⟩
  have hcompactSub : Icc ρ 1 ⊆ Ioc (0 : ℝ) 1 := by
    intro r hr
    exact ⟨hρ.1.trans_le hr.1, hr.2⟩
  have hFcompact : ContinuousOn F (Icc ρ 1) := by
    intro r hr
    exact (hderiv r (hcompactSub hr)).continuousAt.continuousWithinAt
  have hDcompact : ContinuousOn D (Icc ρ 1) := hDcont.mono hcompactSub
  obtain ⟨δ, hδ, hδslope, L, hdense⟩ := dense_case_uniform
    (F := F) (D := D) (M := M) (X := X) (Y := Y)
    (ε := ε / 2) (ρ := ρ) (by linarith) hρIoc hFcompact hDcompact
    (fun r hr => hDpos r (hcompactSub hr))
    (fun r hr => hM r (hcompactSub hr))
    (fun r hr => hX r (hcompactSub hr))
    (fun r hr => hY r (hcompactSub hr))
    (fun r hr => hXeq r (hcompactSub hr))
    (fun r hr => hregion r (hcompactSub hr))
    (fun r hr => hslack r (hcompactSub hr))
  obtain ⟨Kstep, hstep⟩ := exists_descent_floor_step
    (F := F) (D := D) (ε := ε) (δ := δ) (ρ := ρ)
    hε hδ hρ hderiv hDcont hFnonneg
  have hfactorTendsto :
      Tendsto (fun k : ℕ => Real.exp ((ε / 2) * (k : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith))
  obtain ⟨Kfactor, hfactorAfter⟩ :
      ∃ Kfactor : ℕ, ∀ k ≥ Kfactor,
        2 ≤ Real.exp ((ε / 2) * (k : ℝ)) :=
    eventually_atTop.mp (hfactorTendsto.eventually_ge_atTop 2)
  obtain ⟨Kscale, hscaleChoice⟩ :
      ∃ Kscale : ℕ, max ((L : ℝ) / ρ) (2 / ρ) < Kscale := exists_nat_gt _
  let K : ℕ := max Kstep (max Kfactor Kscale)
  filter_upwards [eventually_ge_atTop K] with k hkLarge
  have hKstep : Kstep ≤ k := (le_max_left _ _).trans hkLarge
  have hKfactorLe : Kfactor ≤ k :=
    (le_max_left Kfactor Kscale).trans ((le_max_right Kstep _).trans hkLarge)
  have hKscaleLe : Kscale ≤ k :=
    (le_max_right Kfactor Kscale).trans ((le_max_right Kstep _).trans hkLarge)
  have hKscaleReal : (Kscale : ℝ) ≤ (k : ℝ) := by exact_mod_cast hKscaleLe
  have hscaleBound : max ((L : ℝ) / ρ) (2 / ρ) < (k : ℝ) :=
    hscaleChoice.trans_le hKscaleReal
  have hLscale : (L : ℝ) / ρ < (k : ℝ) :=
    (le_max_left _ _).trans_lt hscaleBound
  have hTwoScale : 2 / ρ < (k : ℝ) :=
    (le_max_right _ _).trans_lt hscaleBound
  have hfactor : 2 ≤ Real.exp ((ε / 2) * (k : ℝ)) :=
    hfactorAfter k hKfactorLe
  have hfloorBound : ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
      RamseyBound k ℓ
        ⌊Real.exp ((F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ))⌋₊ := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | h ℓ ih =>
        intro hℓ hℓk
        have hk : 0 < k := hℓ.trans_le hℓk
        have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
        let r : ℝ := (ℓ : ℝ) / (k : ℝ)
        have hrIoc : r ∈ Ioc (0 : ℝ) 1 := by
          simpa [r] using ratio_mem_Ioc_descent hℓ hℓk
        by_cases hratioSmall : r ≤ ρ
        · apply (ramseyNumber_spec k ℓ).mono
          rw [Nat.le_floor_iff' (ramseyNumber_pos hk hℓ).ne']
          calc
            (ramseyNumber k ℓ : ℝ) ≤ Real.exp ((ε / 2) * (k : ℝ)) :=
              hsmall k ℓ hℓ hℓk (by simpa [r] using hratioSmall)
            _ ≤ Real.exp ((F r + ε) * (k : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hFr := hFnonneg r hrIoc
              nlinarith [mul_nonneg hFr (Nat.cast_nonneg k)]
            _ = Real.exp
                ((F ((ℓ : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := by rfl
        · have hrho : ρ ≤ r := (lt_of_not_ge hratioSmall).le
          have hratioLower : ρ * (k : ℝ) ≤ (ℓ : ℝ) :=
            (le_div_iff₀ hkReal).mp (by simpa [r] using hrho)
          have hLreal : (L : ℝ) < (ℓ : ℝ) := by
            have hLk : (L : ℝ) < ρ * (k : ℝ) := by
              have := (div_lt_iff₀ hρ.1).mp hLscale
              nlinarith
            exact hLk.trans_le hratioLower
          have hLℓ : L ≤ ℓ := by exact_mod_cast hLreal.le
          have hTwoReal : (2 : ℝ) < (ℓ : ℝ) := by
            have hTwoK : (2 : ℝ) < ρ * (k : ℝ) := by
              have := (div_lt_iff₀ hρ.1).mp hTwoScale
              nlinarith
            exact hTwoK.trans_le hratioLower
          have hℓTwo : 2 ≤ ℓ := by exact_mod_cast hTwoReal.le
          have hrCompact : r ∈ Icc ρ 1 := ⟨hrho, hrIoc.2⟩
          let B : ℝ := Real.exp ((F r + ε) * (k : ℝ))
          let N : ℕ := ⌊B⌋₊
          have hA : 0 ≤ F r + ε / 2 := by
            have hFr := hFnonneg r hrIoc
            linarith
          have horderDense :
              Real.exp ((F r + ε / 2) * (k : ℝ)) ≤ (N : ℝ) := by
            dsimp [N, B]
            convert exp_mul_le_floor_exp_add_mul
              (A := F r + ε / 2) (d := ε / 2) hA hfactor using 1
            ring_nf
          have hNreal : 0 < (N : ℝ) :=
            (Real.exp_pos _).trans_le horderDense
          have hNpos : 0 < N := by exact_mod_cast hNreal
          letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
          intro G
          by_cases hredDensity :
              1 - Real.exp (-D r + δ) ≤ redGraphDensity G
          · exact hdense hk hℓ hℓk hratioLower hLℓ
              (by simpa [r, N] using horderDense) (by simpa [r] using hredDensity)
          · have hredDensity' :
                redGraphDensity G < 1 - Real.exp (-D r + δ) :=
              lt_of_not_ge hredDensity
            obtain ⟨v, hv⟩ := exists_compl_degree_gt_of_redGraphDensity_lt
              (G := G) (q := Real.exp (-D r + δ)) hredDensity'
            have hstepBound := hstep hKstep hℓTwo hℓk hratioLower
              (by simpa [r] using hδslope r hrCompact)
            let B₀ : ℝ :=
              Real.exp
                ((F (((ℓ - 1 : ℕ) : ℝ) / (k : ℝ)) + ε) * (k : ℝ))
            have hB₀degree : B₀ < (Gᶜ.degree v : ℝ) := by
              dsimp [B₀]
              exact hstepBound.trans_lt (by simpa [N, B, r] using hv)
            have hfloorB₀ : ⌊B₀⌋₊ ≤ Gᶜ.degree v := by
              have hfloorCast : (⌊B₀⌋₊ : ℝ) ≤ B₀ :=
                Nat.floor_le (Real.exp_pos _).le
              exact_mod_cast (hfloorCast.trans hB₀degree.le)
            have hprevPos : 0 < ℓ - 1 := by omega
            have hprevLe : ℓ - 1 ≤ k := (Nat.sub_le ℓ 1).trans hℓk
            have hprevBound : RamseyBound k (ℓ - 1) ⌊B₀⌋₊ := by
              simpa [B₀] using ih (ℓ - 1) (by omega) hprevPos hprevLe
            have hcard : ⌊B₀⌋₊ ≤ #(Gᶜ.neighborFinset v) := by
              simpa [SimpleGraph.card_neighborFinset_eq_degree] using hfloorB₀
            rcases (hprevBound.mono hcard).on_finset G (Gᶜ.neighborFinset v) rfl with
              hred | hblue
            · exact Or.inl (hasRedClique_mono (Finset.subset_univ _) hred)
            · right
              apply hasBlueClique_mono
                (Finset.subset_univ (insert v (Gᶜ.neighborFinset v)))
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] using
                hasBlueClique_insert_of_subset_neighborFinset hblue Finset.Subset.rfl
  intro ℓ hℓ hℓk
  have hbound := hfloorBound ℓ hℓ hℓk
  exact (Nat.cast_le.mpr (ramseyNumber_le hbound)).trans
    (Nat.floor_le (Real.exp_pos _).le)

end RamseyLean
