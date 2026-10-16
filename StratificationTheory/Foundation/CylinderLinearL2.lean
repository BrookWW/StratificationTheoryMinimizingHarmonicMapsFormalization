module

public import StratificationTheory.Foundation.CylinderPointCoordinates
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import StratificationTheory.Foundation.CylinderSurfaceMeasure

/-!
# Native L2 for affine cylinder interpolation

The exact native surface-product measure identity transfers angular-time L2
data to the physical cylinder. Affine interpolation in time of two angular
L2 maps is consequently in native cylinder L2.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory

private theorem measurableEmbedding_cylinder_param (n : ℕ) :
    MeasurableEmbedding (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let c := (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Domain n)) τ.symm).trans e.symm
  have h := c.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe (s := sphere (0 : Domain n) 1)
      isClosed_sphere.measurableSet).prodMap MeasurableEmbedding.id)
  have heq : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) =
        c ∘ Prod.map Subtype.val id := by
    funext p
    change e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2) =
      e.symm (p.1.val, τ.symm p.2)
    congr 2
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  rw [heq]
  exact h

/-- Angular-time L2 data agreeing with the actual cylinder parametrization
give L2 on its native Euclidean Hausdorff measure. -/
theorem memLp_two_unitCylinder_of_param {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (v : unitCylinder n a b → E) (f : sphere (0 : Domain n) 1 × ℝ → E)
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
    (heq : ∀ (θ : sphere (0 : Domain n) 1) (t : Icc a b),
      v ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) t.val), unitCylinder_param_mem θ t⟩ =
          f (θ, t.val)) :
    MemLp v 2 (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  classical
  let C := unitCylinder n a b
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let u : Domain (n + 1) → E := fun y => if hy : y ∈ C then v ⟨y, hy⟩ else 0
  let p := fun z : sphere (0 : Domain n) 1 × ℝ =>
    e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2)
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have htime : ∀ᵐ z ∂σ.prod ν, z.2 ∈ Icc a b := by
    exact Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  have hup : MemLp (u ∘ p) 2 (σ.prod ν) := hf.ae_eq (htime.mono (by
    intro z hz
    let t : Icc a b := ⟨z.2, hz⟩
    have hp : p z ∈ C := unitCylinder_param_mem z.1 t
    change f z = if hy : p z ∈ C then v ⟨p z, hy⟩ else 0
    rw [dif_pos hp]
    exact (heq z.1 t).symm))
  have hu : MemLp u 2 ((Measure.euclideanHausdorffMeasure n :
      Measure (Domain (n + 1))).restrict C) := by
    rw [← map_cylinder_surface_product_Icc_eq_native_unitCylinder hn a b]
    exact (measurableEmbedding_cylinder_param n).memLp_map_measure_iff.mpr hup
  have hC : MeasurableSet C := (isClosed_native_cylinder_surface_Icc n a b).measurableSet
  have hmap : Measure.map (Subtype.val : C → Domain (n + 1))
      (Measure.euclideanHausdorffMeasure n : Measure C) =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C := by
    simpa only [Subtype.range_coe] using
      (Isometry.map_euclideanHausdorffMeasure (d := n)
        (isometry_subtype_coe : Isometry (Subtype.val : C → Domain (n + 1))))
  rw [← hmap] at hu
  have hv := (MeasurableEmbedding.subtype_coe hC).memLp_map_measure_iff.mp hu
  have huv : u ∘ (Subtype.val : C → Domain (n + 1)) = v := by
    funext y
    exact dif_pos y.property
  rwa [huv] at hv

/-- Affine interpolation of two actual angular L2 maps belongs to native
cylinder L2; no target or Sobolev derivative conclusion is imposed. -/
theorem memLp_two_unitCylinder_linearInterpolation {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (hab : a < b) {u v : sphere (0 : Domain n) 1 → Ambient q}
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MemLp (fun c : unitCylinder n a b =>
      (1 - ((e c.val).2 0 - a) / (b - a)) • u ⟨(e c.val).1, c.property.1⟩ +
        (((e c.val).2 0 - a) / (b - a)) • v ⟨(e c.val).1, c.property.1⟩) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  intro e
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Icc a b)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  let w : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p =>
    (1 - (p.2 - a) / (b - a)) • u p.1 + ((p.2 - a) / (b - a)) • v p.1
  have hbound : ∀ᵐ t ∂ν, 0 ≤ (t - a) / (b - a) ∧ (t - a) / (b - a) ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2 a)⟩
  have hα : MemLp (fun t : ℝ => (t - a) / (b - a)) ∞ ν := by
    apply memLp_top_of_bound (f := fun t : ℝ => (t - a) / (b - a))
      ((continuous_id.sub continuous_const).div_const (b - a)).aestronglyMeasurable 1
    exact hbound.mono (fun t ht => by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2)
  have hβ : MemLp (fun t : ℝ => 1 - (t - a) / (b - a)) ∞ ν :=
    (memLp_const (1 : ℝ)).sub hα
  have hw : MemLp w 2 (σ.prod ν) :=
    ((hu.comp_fst ν).smul (hβ.comp_snd σ)).add ((hv.comp_fst ν).smul (hα.comp_snd σ))
  apply memLp_two_unitCylinder_of_param hn _ w hw
  intro θ t
  dsimp only [e, w]
  simp only [ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true]

end StratificationTheory
