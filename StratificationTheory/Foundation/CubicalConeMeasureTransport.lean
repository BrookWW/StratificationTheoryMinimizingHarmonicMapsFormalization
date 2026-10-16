module

public import StratificationTheory.Foundation.CubicalConeMeasure
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Original a.e. classes in positive face-cone coordinates

The inverse cone coordinates pull back native product null sets to native
cone null sets. This transfers the original measurable classes without
selecting new pointwise representatives.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Inverse positive cone coordinates are nonsingular for the original
native base-time product measure on any measurable base and positive time set. -/
theorem quasiMeasurePreserving_inverse_positive_cone {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) :
    Measure.QuasiMeasurePreserving
      (fun p : Domain n × ℝ => (p.2⁻¹ • p.1, p.2))
      (((volume : Measure (Domain n)).prod volume).restrict
        {p | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S})
      ((volume.restrict S).prod (volume.restrict J)) := by
  let C := {p : Domain n × ℝ | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S}
  let Q : Domain n × ℝ → Domain n × ℝ := fun p => (p.2⁻¹ • p.1, p.2)
  let μ := (volume : Measure (Domain n)).restrict S
  let ν := (volume : Measure ℝ).restrict J
  let σ := ((volume : Measure (Domain n)).prod volume).restrict C
  have hQ : Measurable Q := (measurable_snd.inv.smul measurable_fst).prodMk measurable_snd
  refine ⟨hQ, Measure.AbsolutelyContinuous.mk ?_⟩
  intro A hA hAzero
  rw [Measure.map_apply hQ hA]
  let g : Domain n × ℝ → ℝ≥0∞ := A.indicator 1
  have hg : Measurable g := measurable_const.indicator hA
  have hJac := lintegral_product_positive_cone hS hJ hJpos
    ((hg.comp hQ).aemeasurable : AEMeasurable (g ∘ Q) σ)
  have hcomp : (g ∘ Q) = (Q ⁻¹' A).indicator (1 : Domain n × ℝ → ℝ≥0∞) := by
    funext p
    change A.indicator 1 (Q p) = (Q ⁻¹' A).indicator 1 p
    by_cases hp : Q p ∈ A
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem (show p ∈ Q ⁻¹' A from hp)]
      rfl
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ Q ⁻¹' A from hp)]
  have hbad : (∫⁻ p, (g ∘ Q) p ∂σ) = σ (Q ⁻¹' A) := by
    rw [hcomp, lintegral_indicator_one (hA.preimage hQ)]
  have hforward (t : ℝ) (ht : t ∈ J) (x : Domain n) : Q (t • x, t) = (x, t) := by
    dsimp only [Q]
    rw [smul_smul, inv_mul_cancel₀ (hJpos t ht).ne', one_smul]
  have hRHS :
      (∫⁻ t in J, ENNReal.ofReal (t ^ n) * ∫⁻ x in S, (g ∘ Q) (t • x, t)) =
        ∫⁻ t, ENNReal.ofReal (t ^ n) * ∫⁻ x, g (x, t) ∂μ ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hJ] with t ht
    congr 1
    apply lintegral_congr_ae
    exact Eventually.of_forall (fun x => congrArg g (hforward t ht x))
  have hInner : Measurable (fun t : ℝ => ∫⁻ x, g (x, t) ∂μ) := hg.lintegral_prod_left'
  have hZero : (∫⁻ p, g p ∂μ.prod ν) = 0 := by
    rw [lintegral_indicator_one hA]
    exact hAzero
  have hInnerZero : (∫⁻ t, ∫⁻ x, g (x, t) ∂μ ∂ν) = 0 :=
    (lintegral_prod_symm g hg.aemeasurable).symm.trans hZero
  have hAE := (lintegral_eq_zero_iff hInner).mp hInnerZero
  have hWeightedZero : (∫⁻ t, ENNReal.ofReal (t ^ n) * ∫⁻ x, g (x, t) ∂μ ∂ν) = 0 := by
    calc
      _ = ∫⁻ _t, (0 : ℝ≥0∞) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hAE] with t ht
        rw [ht, Pi.zero_apply, mul_zero]
      _ = 0 := lintegral_zero
  rw [← hbad]
  exact hJac.trans (hRHS.trans hWeightedZero)

end StratificationTheory
