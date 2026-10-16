module

public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import StratificationTheory.Foundation.DominatedL2Pullback

/-!
# Bounded native inverse-cone measure with independent parameters

Inverse spatial cone coordinates retain their actual height variable. On a
bounded positive-height band their native pushforward is dominated by the
original base-height measure with the true height-to-dimension factor.
An arbitrary independent parameter is carried unchanged.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

theorem map_native_inverse_positive_cone_le_smul {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {M : ℝ} (hJM : ∀ t ∈ J, t ≤ M) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ J ∧ ξ y ∈ S}
    Measure.map (fun y => (ξ y, T y)) (volume.restrict C) ≤
      ENNReal.ofReal (M ^ n) • ((volume.restrict S).prod (volume.restrict J)) := by
  intro e T ξ C
  let Q : Domain (n + 1) → Domain n × ℝ := fun y => (ξ y, T y)
  let μ := (volume : Measure (Domain n)).restrict S
  let ν := (volume : Measure ℝ).restrict J
  have hT : Measurable T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hQ : Measurable Q :=
    (hT.inv.smul (measurable_fst.comp e.continuous.measurable)).prodMk hT
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hQ hA, Measure.smul_apply, smul_eq_mul]
  let f : Domain n × ℝ → ℝ≥0∞ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have hindicator : f ∘ Q = (Q ⁻¹' A).indicator (1 : Domain (n + 1) → ℝ≥0∞) := by
    funext y
    change A.indicator 1 (Q y) = (Q ⁻¹' A).indicator 1 y
    by_cases hy : Q y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ Q ⁻¹' A from hy)]
      rfl
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y ∉ Q ⁻¹' A from hy)]
  have hraw (t : ℝ) (ht : t ∈ J) (x : Domain n) :
      Q (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) = (x, t) := by
    dsimp only [Q, ξ, T]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true, smul_smul,
      inv_mul_cancel₀ (hJpos t ht).ne', one_smul]
  calc
    (volume.restrict C) (Q ⁻¹' A) = ∫⁻ y in C, (f ∘ Q) y := by
      rw [hindicator, lintegral_indicator_one (hA.preimage hQ)]
    _ = ∫⁻ t in J, ENNReal.ofReal (t ^ n) * ∫⁻ x in S,
        (f ∘ Q) (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) :=
      lintegral_native_positive_cone hS hJ hJpos ((hf.comp hQ).aemeasurable)
    _ = ∫⁻ t, ENNReal.ofReal (t ^ n) * ∫⁻ x, f (x, t) ∂μ ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hJ] with t ht
      simp only [Function.comp_apply, hraw t ht]
      rfl
    _ ≤ ∫⁻ t, ENNReal.ofReal (M ^ n) * ∫⁻ x, f (x, t) ∂μ ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hJ] with t ht
      exact mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hJpos t ht).le (hJM t ht) n)) (by positivity)
    _ = ENNReal.ofReal (M ^ n) * ∫⁻ p, f p ∂μ.prod ν := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact (lintegral_prod_symm f hf.aemeasurable).symm
    _ = ENNReal.ofReal (M ^ n) * ((volume.restrict S).prod (volume.restrict J)) A := by
      rw [lintegral_indicator_one hA]

/-- The actual spatial inverse-cone coordinates retain an arbitrary
independent parameter, ordered with the original face base. -/
theorem map_native_inverse_cone_independent_parameter_le_smul {n : ℕ} {A : Type*}
    [MeasurableSpace A] (τ : Measure A) [SFinite τ]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {M : ℝ} (hJM : ∀ t ∈ J, t ≤ M) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ J ∧ ξ y ∈ S}
    Measure.map (fun p : Domain (n + 1) × A => ((ξ p.1, p.2), T p.1))
      ((volume.restrict C).prod τ) ≤
        ENNReal.ofReal (M ^ n) • (((volume.restrict S).prod τ).prod (volume.restrict J)) := by
  intro e T ξ C
  let μ := (volume : Measure (Domain n)).restrict S
  let ν := (volume : Measure ℝ).restrict J
  let Q : Domain (n + 1) → Domain n × ℝ := fun y => (ξ y, T y)
  let P := Prod.map Q (id : A → A)
  let R : (Domain n × ℝ) × A → (Domain n × A) × ℝ := fun p => ((p.1.1, p.2), p.1.2)
  have hT : Measurable T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hQ : Measurable Q :=
    (hT.inv.smul (measurable_fst.comp e.continuous.measurable)).prodMk hT
  have hP : Measurable P := hQ.prodMap measurable_id
  have hR : MeasurePreserving R ((μ.prod ν).prod τ) ((μ.prod τ).prod ν) :=
    ((measurePreserving_prodAssoc μ τ ν).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id μ).prod Measure.measurePreserving_swap).comp
        (measurePreserving_prodAssoc μ ν τ))
  have hsp := map_native_inverse_positive_cone_le_smul hS hJ hJpos hJM
  change Measure.map Q (volume.restrict C) ≤ ENNReal.ofReal (M ^ n) • (μ.prod ν) at hsp
  have hdom : Measure.map P ((volume.restrict C).prod τ) ≤
      ENNReal.ofReal (M ^ n) • ((μ.prod ν).prod τ) := by
    rw [← Measure.map_prod_map (volume.restrict C) τ hQ measurable_id, Measure.map_id]
    simpa only [Measure.prod_smul_left] using Measure.prod_mono hsp (le_refl τ)
  have heq : (fun p : Domain (n + 1) × A => ((ξ p.1, p.2), T p.1)) = R ∘ P := rfl
  rw [heq, ← Measure.map_map hR.measurable hP]
  calc
    _ ≤ Measure.map R (ENNReal.ofReal (M ^ n) • ((μ.prod ν).prod τ)) := Measure.map_mono hdom hR.measurable
    _ = _ := by rw [Measure.map_smul, hR.map_eq]

end StratificationTheory
