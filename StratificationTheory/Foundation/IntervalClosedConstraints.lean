module

public import StratificationTheory.Foundation.BanachIntervalWeakRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.ProjIcc

/-!
# Closed constraints for interval weak representatives

A continuous map on a nondegenerate closed interval preserves any closed
constraint satisfied almost everywhere in the interior. The unique Banach
weak representative therefore retains the original map's a.e. closed constraint
at every interval point, including both endpoints.
-/

public section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- An interior volume-a.e. closed constraint on an actual continuous interval
map holds at every point of the closed interval. -/
theorem continuous_interval_mem_closed_of_ae {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a < b) (F : C(Icc a b, E)) {K : Set E} (hK : IsClosed K)
    (hF : ∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ ∈ K) :
    ∀ t : Icc a b, F t ∈ K := by
  let G : ℝ → E := fun x => F (projIcc a b hab.le x)
  have hG : Continuous G := F.continuous.comp continuous_projIcc
  have hS : IsClosed (G ⁻¹' K) := hK.preimage hG
  have hAe : ∀ᵐ x ∂volume, x ∈ Ioo a b → G x ∈ K := by
    filter_upwards [hF] with x hx hxI
    change F (projIcc a b hab.le x) ∈ K
    rw [projIcc_of_mem hab.le ⟨hxI.1.le, hxI.2.le⟩]
    exact hx hxI
  have hnull : volume (Ioo a b ∩ (G ⁻¹' K)ᶜ) = 0 := by
    rw [ae_iff] at hAe
    convert hAe using 1
    congr 1
    ext x
    simp only [Classical.not_imp, mem_inter_iff, mem_compl_iff, mem_preimage, mem_setOf_eq]
  have hEmpty : Ioo a b ∩ (G ⁻¹' K)ᶜ = ∅ :=
    (isOpen_Ioo.inter hS.isOpen_compl).eq_empty_of_measure_zero hnull
  have hInterior : Ioo a b ⊆ G ⁻¹' K := by
    intro x hx
    by_contra hnot
    have hmem : x ∈ Ioo a b ∩ (G ⁻¹' K)ᶜ := ⟨hx, hnot⟩
    rw [hEmpty] at hmem
    exact hmem.elim
  have hClosed : Icc a b ⊆ G ⁻¹' K := by
    rw [← closure_Ioo hab.ne]
    exact closure_minimal hInterior hS
  intro t
  have ht := hClosed t.property
  change F (projIcc a b hab.le (t : ℝ)) ∈ K at ht
  rw [projIcc_of_mem hab.le t.property] at ht
  exact ht

/-- Actual Banach L2 weak data admit the same unique continuous representative,
with all integral and energy properties and the original a.e. closed constraint
holding pointwise through both endpoints. -/
theorem banach_interval_weakDerivative_exists_unique_closed_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • f x) = -(∫ x, φ x • g x))
    {K : Set E} (hK : IsClosed K)
    (hfK : ∀ᵐ x ∂volume.restrict (Ioo a b), f x ∈ K) :
    ∃! F : C(Icc a b, E),
      (∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ = f x) ∧
      (∃ G : ℝ → E, AbsolutelyContinuousOnInterval G a b ∧
        ∀ x : Icc a b, G x = F x) ∧
      (∀ s t : Icc a b, F t - F s = ∫ y in (s : ℝ)..(t : ℝ), g y) ∧
      (∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤
        |(t : ℝ) - (s : ℝ)| * ∫ y in Ioo a b, ‖g y‖ ^ 2) ∧
      (∀ t : Icc a b, ‖F t‖ ^ 2 ≤ (2 / (b - a)) * (∫ y in Ioo a b, ‖f y‖ ^ 2) +
        2 * (b - a) * (∫ y in Ioo a b, ‖g y‖ ^ 2)) ∧
      ∀ t : Icc a b, F t ∈ K := by
  obtain ⟨F, hF, hUnique⟩ :=
    banach_interval_weakDerivative_exists_unique_continuous_representative hab hf hg hw
  have hFAe : ∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ ∈ K := by
    filter_upwards [hF.1, (ae_restrict_iff' measurableSet_Ioo).mp hfK] with x hx hmem hxI
    rw [hx hxI]
    exact hmem hxI
  have hFK := continuous_interval_mem_closed_of_ae hab F hK hFAe
  refine ⟨F, ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2, hFK⟩, ?_⟩
  intro H hH
  exact hUnique H ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, hH.2.2.2.2.1⟩

end StratificationTheory
