module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Native volume in positive face-cone coordinates

Fixed positive spatial dilations have their exact dimension power. Product
integration then supplies the native Jacobian of the face-cone parametrization.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Module
open scoped Topology ENNReal
namespace StratificationTheory

/-- An inverse positive dilation contributes its exact native volume power
to every nonnegative integral, with no representative replacement. -/
theorem lintegral_domain_inverse_smul {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : Domain n → ℝ≥0∞) :
    (∫⁻ x, f (r⁻¹ • x)) = ENNReal.ofReal (r ^ n) * ∫⁻ x, f x := by
  have hr0 : r ≠ 0 := hr.ne'
  let H : Domain n ≃ₜ Domain n := Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr0))
  have hH : MeasurableEmbedding (fun x : Domain n => r⁻¹ • x) := by
    exact H.measurableEmbedding
  have hm := Measure.map_addHaar_smul (volume : Measure (Domain n)) (inv_ne_zero hr0)
  have h := hH.lintegral_map (μ := (volume : Measure (Domain n))) f
  rw [hm, lintegral_smul_measure, smul_eq_mul] at h
  simpa only [Domain, finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv,
    abs_of_nonneg (pow_nonneg hr.le n)] using h.symm

/-- Integrating over one actual dilated face has the exact positive
Jacobian r^n times the original face integral. -/
theorem lintegral_inverse_smul_face {n : ℕ} {r : ℝ} (hr : 0 < r)
    {S : Set (Domain n)} (hS : MeasurableSet S) (f : Domain n → ℝ≥0∞) :
    (∫⁻ x in {x | r⁻¹ • x ∈ S}, f x) =
      ENNReal.ofReal (r ^ n) * ∫⁻ x in S, f (r • x) := by
  have hpre : MeasurableSet {x : Domain n | r⁻¹ • x ∈ S} :=
    hS.preimage (continuous_const_smul r⁻¹).measurable
  have hEq (x : Domain n) :
      ({x : Domain n | r⁻¹ • x ∈ S}.indicator f) x =
        (S.indicator (fun y => f (r • y))) (r⁻¹ • x) := by
    by_cases hx : r⁻¹ • x ∈ S
    · rw [Set.indicator_of_mem (show x ∈ {x : Domain n | r⁻¹ • x ∈ S} from hx),
        Set.indicator_of_mem hx, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Domain n | r⁻¹ • x ∈ S} from hx),
        Set.indicator_of_notMem hx]
  rw [← lintegral_indicator hpre]
  simp_rw [hEq]
  rw [lintegral_domain_inverse_smul hr, lintegral_indicator hS]

/-- The positive face-cone parametrization has native Jacobian t^n. The
source base and time set are arbitrary measurable sets with positive time. -/
theorem lintegral_product_positive_cone {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {f : Domain n × ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (((volume : Measure (Domain n)).prod volume).restrict
      {p | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S})) :
    (∫⁻ p in {p : Domain n × ℝ | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S}, f p
      ∂((volume : Measure (Domain n)).prod volume)) =
      ∫⁻ t in J, ENNReal.ofReal (t ^ n) * ∫⁻ x in S, f (t • x, t) := by
  let C := {p : Domain n × ℝ | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S}
  have hC : MeasurableSet C :=
    (hJ.preimage measurable_snd).inter (hS.preimage (measurable_snd.inv.smul measurable_fst))
  have hfm : AEMeasurable (C.indicator f) ((volume : Measure (Domain n)).prod volume) :=
    (aemeasurable_indicator_iff hC).mpr hf
  rw [← lintegral_indicator hC, lintegral_prod_symm _ hfm, ← lintegral_indicator hJ]
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro t
  by_cases ht : t ∈ J
  · rw [Set.indicator_of_mem ht]
    have hpre : MeasurableSet {x : Domain n | t⁻¹ • x ∈ S} :=
      hS.preimage (continuous_const_smul t⁻¹).measurable
    calc
      _ = ∫⁻ x in {x : Domain n | t⁻¹ • x ∈ S}, f (x, t) := by
        rw [← lintegral_indicator hpre]
        apply lintegral_congr_ae
        apply Eventually.of_forall
        intro x
        change C.indicator f (x, t) = {x : Domain n | t⁻¹ • x ∈ S}.indicator (fun x => f (x, t)) x
        by_cases hx : t⁻¹ • x ∈ S
        · rw [Set.indicator_of_mem (show (x, t) ∈ C from ⟨ht, hx⟩),
            Set.indicator_of_mem (show x ∈ {x : Domain n | t⁻¹ • x ∈ S} from hx)]
        · rw [Set.indicator_of_notMem (show (x, t) ∉ C from fun h => hx h.2),
            Set.indicator_of_notMem (show x ∉ {x : Domain n | t⁻¹ • x ∈ S} from hx)]
      _ = _ := lintegral_inverse_smul_face (hJpos t ht) hS (fun x => f (x, t))
  · rw [Set.indicator_of_notMem ht]
    have hz : (fun x : Domain n => C.indicator f (x, t)) = 0 := by
      funext x
      exact Set.indicator_of_notMem (show (x, t) ∉ C from fun h => ht h.1) f
    change (∫⁻ x : Domain n, C.indicator f (x, t)) = 0
    rw [hz]
    exact lintegral_zero

end StratificationTheory
