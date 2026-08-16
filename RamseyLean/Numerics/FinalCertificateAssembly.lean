import RamseyLean.Numerics.FinalCertificateCoverage

/-!
# Assembly of the final branch certificate

The fixed meshes overlap slightly around the two irrational frontier
crossings.  This module records the continuum conclusions of those meshes and
performs the purely analytic branch routing required by
`FinalNumericalCertificate`.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set

noncomputable section

/-- Continuum-level conclusions supplied by the checked fixed-point meshes. -/
structure FinalContinuumCertificate : Prop where
  small :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 → r ≤ (258 / 1000 : ℝ) →
      finalSmallParameter r ∈ Ioc (0 : ℝ) 1 ∧
        finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB)
          (finalSmallParameter r) ∧
        0 < finalSmallNormalizedSlack r
  middle :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      (2578 / 10000 : ℝ) ≤ r → r ≤ (3606 / 10000 : ℝ) →
      0 < finalMiddleNormalizedSlack r
  cap :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      (3604 / 10000 : ℝ) ≤ r → r ≤ (361 / 1000 : ℝ) →
      0 < finalLargeCapNormalizedSlack r
  large :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 → (361 / 1000 : ℝ) ≤ r →
      finalLargeParameter r ∈ Ioc (0 : ℝ) 1 ∧
        finalX r ≤ frontierA (FSlope preliminaryB)
          (finalLargeParameter r) ∧
        0 < finalLargeNormalizedSlack r
  bBelow :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 → r ≤ (2578 / 10000 : ℝ) →
      frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r
  bAbove :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 → (258 / 1000 : ℝ) ≤ r →
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB) 1
  aBelow :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 → r ≤ (3604 / 10000 : ℝ) →
      frontierA (FSlope preliminaryB) 1 ≤ finalX r
  aAbove :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 → (3605 / 10000 : ℝ) ≤ r →
      finalX r < frontierA (FSlope preliminaryB) 1

/-- Route the exact frontier hypotheses through the overlapping checked
meshes. -/
theorem finalNumericalCertificate_of_continuum
    (h : FinalContinuumCertificate) : FinalNumericalCertificate := by
  refine
    { small_parameter_mem := ?_
      small_coordinate := ?_
      large_parameter_mem := ?_
      large_coordinate := ?_
      small_slack_pos := ?_
      middle_slack_pos := ?_
      large_cap_slack_pos := ?_
      large_slack_pos := ?_ }
  · intro r hr hsmall
    have hrCut : r ≤ (258 / 1000 : ℝ) := by
      by_contra hn
      have hAbove := h.bAbove hr (le_of_not_ge hn)
      exact (not_lt_of_ge hAbove) hsmall
    exact (h.small hr hrCut).1
  · intro r hr hsmall
    have hrCut : r ≤ (258 / 1000 : ℝ) := by
      by_contra hn
      have hAbove := h.bAbove hr (le_of_not_ge hn)
      exact (not_lt_of_ge hAbove) hsmall
    exact (h.small hr hrCut).2.1
  · intro r hr hcut _hlarge
    exact (h.large hr hcut.le).1
  · intro r hr hcut _hlarge
    exact (h.large hr hcut.le).2.1
  · intro r hr hsmall
    have hrCut : r ≤ (258 / 1000 : ℝ) := by
      by_contra hn
      have hAbove := h.bAbove hr (le_of_not_ge hn)
      exact (not_lt_of_ge hAbove) hsmall
    exact (h.small hr hrCut).2.2
  · intro r hr hnotSmall hmiddle
    have hrLower : (2578 / 10000 : ℝ) ≤ r := by
      by_contra hn
      have hBelow := h.bBelow hr (le_of_not_ge hn)
      exact hnotSmall hBelow
    have hrUpper : r ≤ (3606 / 10000 : ℝ) := by
      by_contra hn
      have hAbove : (3605 / 10000 : ℝ) ≤ r := by
        have : (3605 / 10000 : ℝ) < 3606 / 10000 := by norm_num
        linarith
      have hCross := h.aAbove hr hAbove
      exact (not_lt_of_ge hmiddle) hCross
    exact h.middle hr hrLower hrUpper
  · intro r hr hlarge hcap
    have hrLower : (3604 / 10000 : ℝ) ≤ r := by
      by_contra hn
      have hBelow := h.aBelow hr (le_of_not_ge hn)
      exact (not_lt_of_ge hBelow) hlarge
    exact h.cap hr hrLower hcap
  · intro r hr hcut _hlarge
    exact (h.large hr hcut.le).2.2

end

end RamseyLean.FinalCertificate
