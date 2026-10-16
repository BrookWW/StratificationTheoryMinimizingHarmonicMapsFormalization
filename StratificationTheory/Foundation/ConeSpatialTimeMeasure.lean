module

public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Native spatial cone coordinates with an independent time variable

The inverse spatial cone map has its exact native base pushforward. Taking
its product with the identity preserves an independent time coordinate and
the same dimension power, without dilating the interpolation time.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Dropping the positive radial coordinate has exactly the integrated cone
Jacobian as its native measure multiplier on the original base. -/
theorem map_native_positive_cone_base {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let ξ : Domain (n + 1) → Domain n := fun y => ((e y).2 0)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ξ y ∈ S}
    Measure.map ξ (volume.restrict C) =
      (∫⁻ t in J, ENNReal.ofReal (t ^ n)) • volume.restrict S := by
  intro e ξ C
  have hT : Measurable (fun y : Domain (n + 1) => (e y).2 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hX : Measurable (fun y : Domain (n + 1) => (e y).1) :=
    measurable_fst.comp e.continuous.measurable
  have hξ : Measurable ξ := hT.inv.smul hX
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hξ hA, Measure.smul_apply, smul_eq_mul]
  let g : Domain n → ℝ≥0∞ := A.indicator 1
  have hg : Measurable g := measurable_const.indicator hA
  have hgξ : Measurable (g ∘ ξ) := hg.comp hξ
  have hindicator : (g ∘ ξ) = (ξ ⁻¹' A).indicator (1 : Domain (n + 1) → ℝ≥0∞) := by
    funext y
    change A.indicator 1 (ξ y) = (ξ ⁻¹' A).indicator 1 y
    by_cases hy : ξ y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ ξ ⁻¹' A from hy)]
      rfl
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show y ∉ ξ ⁻¹' A from hy)]
  have hraw (t : ℝ) (ht : t ∈ J) (x : Domain n) :
      ξ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) = x := by
    dsimp only [ξ]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true, smul_smul,
      inv_mul_cancel₀ (hJpos t ht).ne', one_smul]
  calc
    (volume.restrict C) (ξ ⁻¹' A) = ∫⁻ y in C, (g ∘ ξ) y := by
      rw [hindicator, lintegral_indicator_one (hA.preimage hξ)]
    _ = ∫⁻ t in J, ENNReal.ofReal (t ^ n) * ∫⁻ x in S,
          (g ∘ ξ) (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) :=
      lintegral_native_positive_cone hS hJ hJpos hgξ.aemeasurable
    _ = ∫⁻ t in J, ENNReal.ofReal (t ^ n) * (volume.restrict S) A := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hJ] with t ht
      simp only [Function.comp_def, hraw t ht, g, lintegral_indicator_one hA]
    _ = _ := lintegral_mul_const _ ((measurable_id.pow_const n).ennreal_ofReal)

/-- The same actual spatial cone coordinates retain an independent time
variable with coefficient-one time measure. -/
theorem map_native_positive_cone_base_prod {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) (ν : Measure ℝ) [SFinite ν] :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let ξ : Domain (n + 1) → Domain n := fun y => ((e y).2 0)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ξ y ∈ S}
    Measure.map (fun p : Domain (n + 1) × ℝ => (ξ p.1, p.2))
      ((volume.restrict C).prod ν) =
      (∫⁻ t in J, ENNReal.ofReal (t ^ n)) • ((volume.restrict S).prod ν) := by
  intro e ξ C
  have hT : Measurable (fun y : Domain (n + 1) => (e y).2 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hξ : Measurable ξ := hT.inv.smul (measurable_fst.comp e.continuous.measurable)
  calc
    _ = (Measure.map ξ (volume.restrict C)).prod ν := by
      have heq : (fun p : Domain (n + 1) × ℝ => (ξ p.1, p.2)) = Prod.map ξ id := by
        funext p
        cases p
        rfl
      rw [heq, ← Measure.map_prod_map (volume.restrict C) ν hξ measurable_id, Measure.map_id]
    _ = _ := by rw [map_native_positive_cone_base hS hJ hJpos, Measure.prod_smul_left]

/-- Spatial inverse cone coordinates, with interpolation time unchanged,
have the same exact native Jacobian in the actual Euclidean models. -/
theorem map_euclidean_spatial_cone_time {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S)
    {J I : Set ℝ} (hJ : MeasurableSet J) (hI : MeasurableSet I)
    (hJpos : ∀ t ∈ J, 0 < t) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let ξ : Domain (n + 1) → Domain n := fun y => ((e y).2 0)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ξ y ∈ S}
    let V := {y : Domain (n + 1 + 1) | (E y).1 ∈ C ∧ (E y).2 0 ∈ I}
    let B := {z : Domain (n + 1) | (e z).1 ∈ S ∧ (e z).2 0 ∈ I}
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm (ξ ((E y).1), (E y).2)
    Measure.map F (volume.restrict V) =
      (∫⁻ r in J, ENNReal.ofReal (r ^ n)) • volume.restrict B := by
  intro e E ξ C V B F
  let P : Domain (n + 1 + 1) → Domain (n + 1) × ℝ := fun y => ((E y).1, (E y).2 0)
  let Q : Domain (n + 1) × ℝ → Domain n × ℝ := fun p => (ξ p.1, p.2)
  let R : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  have hPm : Measurable P := (measurePreserving_cylinder_coordinates (n + 1)).measurable
  have hRm : Measurable R := (measurePreserving_cylinder_coordinates_inverse n).measurable
  have hT : Measurable (fun y : Domain (n + 1) => (e y).2 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hX : Measurable (fun y : Domain (n + 1) => (e y).1) :=
    measurable_fst.comp e.continuous.measurable
  have hξ : Measurable ξ := hT.inv.smul hX
  have hQm : Measurable Q := (hξ.comp measurable_fst).prodMk measurable_snd
  have hC : MeasurableSet C := (hJ.preimage hT).inter (hS.preimage hξ)
  have hB : MeasurableSet B := (hS.preimage hX).inter (hI.preimage hT)
  have hMP := (measurePreserving_cylinder_coordinates (n + 1)).restrict_preimage (hC.prod hI)
  change MeasurePreserving P (volume.restrict V)
    (((volume : Measure (Domain (n + 1))).prod volume).restrict (C ×ˢ I)) at hMP
  rw [← Measure.prod_restrict] at hMP
  have hRP := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hB
  have hpre : R ⁻¹' B = S ×ˢ I := by
    ext p
    simp only [R, B, mem_preimage, mem_setOf_eq, e.apply_symm_apply,
      PiLp.single_apply, ite_true, mem_prod]
  change MeasurePreserving R
    (((volume : Measure (Domain n)).prod volume).restrict (R ⁻¹' B))
    (volume.restrict B) at hRP
  rw [hpre, ← Measure.prod_restrict] at hRP
  have hF : F = R ∘ Q ∘ P := by
    funext y
    dsimp only [F, R, Q, P, Function.comp_def]
    apply congrArg e.symm
    apply Prod.ext
    · rfl
    · ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.single_apply, ite_true]
  calc
    _ = Measure.map R (Measure.map Q (Measure.map P (volume.restrict V))) := by
      rw [Measure.map_map hQm hPm, Measure.map_map hRm (hQm.comp hPm), hF]
    _ = Measure.map R (Measure.map Q ((volume.restrict C).prod (volume.restrict I))) :=
      congrArg (fun μ => Measure.map R (Measure.map Q μ)) hMP.map_eq
    _ = Measure.map R ((∫⁻ r in J, ENNReal.ofReal (r ^ n)) •
          ((volume.restrict S).prod (volume.restrict I))) := by
      rw [map_native_positive_cone_base_prod hS hJ hJpos (volume.restrict I)]
    _ = _ := by rw [Measure.map_smul, hRP.map_eq]

end StratificationTheory
