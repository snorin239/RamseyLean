import RamseyLean.Numerics.PreliminaryCertificateSound
import RamseyLean.Numerics.PreliminaryCertificateMesh

set_option autoImplicit false

namespace RamseyLean.PreliminaryCertificate

open Set
open FixedPointInterval

noncomputable section

/-- A checked positive-row certificate proves positivity throughout its input
interval. The positive lower endpoint is recovered from the row's own entropy
safety check. -/
theorem normalized_pos_of_checkPositive {I : Interval} {row : Row} {r : ℝ}
    (hcheck : checkPositive I row = true) (hrI : I.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryNormalizedSlack r := by
  have hfacts := PositiveFacts.of_check hcheck
  have hsafety := EntropySafety.of_check hfacts.entropySafe
  have haPos : 0 < row.entropy.a.lo := by
    simpa only [positive, decide_eq_true_eq] using hsafety.aPos
  have hIloInt : 0 < I.lo := by
    rw [hfacts.entropyValid.a] at haPos
    simpa only [point] using haPos
  have hlo : 0 < value I.lo := by
    unfold value
    exact div_pos (by exact_mod_cast hIloInt) scale_pos_real
  exact normalized_pos_of_positive_facts hfacts hrI hr hlo

/-- An origin-row certificate uses the nonsingular full formula and therefore
also covers cells whose fixed-point lower endpoint is zero. -/
theorem normalized_pos_of_checkOrigin {I : Interval} {B : Data} {r : ℝ}
    (hcheck : checkOrigin I B = true) (hrI : I.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryNormalizedSlack r :=
  normalized_pos_of_origin_facts (OriginFacts.of_check hcheck) hrI hr

/-- Continuum bridge for one affine band of cached preliminary-certificate
rows. -/
theorem normalized_pos_on_affine_band {a b : ℤ} {N : ℕ}
    (hab : value a < value b) (hN : 0 < N)
    (hrows : ∀ k : ℕ, k ≤ N → ∃ row : Row,
      checkPositive (affineCell a b N k) row = true)
    {r : ℝ} (hrBand : r ∈ Icc (value a) (value b))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < preliminaryNormalizedSlack r := by
  let u := (r - value a) / (value b - value a)
  let k := ⌊(N : ℝ) * u⌋₊
  have hmesh := UniformMesh.floor_mem_affineMesh hab N hN hrBand
  have hkN : k ≤ N := by simpa [k, u] using hmesh.1
  have hrange : r ∈ Icc
      (UniformMesh.affinePoint (value a) (value b) N k)
      (UniformMesh.affinePoint (value a) (value b) N (k + 1)) := by
    simpa [k, u] using hmesh.2
  obtain ⟨row, hcheck⟩ := hrows k hkN
  have hrCell : (affineCell a b N k).Contains r :=
    affineCell_contains hN hrange
  exact normalized_pos_of_checkPositive hcheck hrCell hr

end

end RamseyLean.PreliminaryCertificate

