module

public import StratificationTheory.Foundation.CylinderPointCoordinates
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import StratificationTheory.Foundation.CylinderSurfaceMeasure

/-!
# Native cylinder integral transport

Integrable angular-time data agreeing with the physical cylinder
parametrization give an integrable function on the actual cylinder subtype.
Its native Hausdorff integral equals the sphere-time product integral exactly.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

private theorem measurableEmbedding_cylinder_integral_param (n : ℕ) :
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

/-- Actual integrable product data transfer to the native physical cylinder,
with equality of the full Bochner integrals and no normalization factor. -/
theorem integrable_unitCylinder_of_param_and_integral {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (v : unitCylinder n a b → E)
    (f : sphere (0 : Domain n) 1 × ℝ → E)
    (hf : Integrable f ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
    (heq : ∀ (θ : sphere (0 : Domain n) 1) (t : Icc a b),
      v ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) t.val), unitCylinder_param_mem θ t⟩ =
          f (θ, t.val)) :
    Integrable v (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      (∫ y : unitCylinder n a b, v y ∂Measure.euclideanHausdorffMeasure n) =
        ∫ p : sphere (0 : Domain n) 1 × ℝ, f p
          ∂((Measure.euclideanHausdorffMeasure (n - 1) :
            Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))) := by
  classical
  let C := unitCylinder n a b
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let u : Domain (n + 1) → E := fun y => if hy : y ∈ C then v ⟨y, hy⟩ else 0
  let p := fun z : sphere (0 : Domain n) 1 × ℝ =>
    e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2)
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let μ := σ.prod ν
  let σC : Measure C := Measure.euclideanHausdorffMeasure n
  let μC := (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C
  have hparam : (u ∘ p) =ᵐ[μ] f := by
    have htime : ∀ᵐ z ∂μ, z.2 ∈ Icc a b :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [htime] with z hz
    let t : Icc a b := ⟨z.2, hz⟩
    have hp : p z ∈ C := unitCylinder_param_mem z.1 t
    change (if hy : p z ∈ C then v ⟨p z, hy⟩ else 0) = f z
    rw [dif_pos hp]
    exact heq z.1 t
  have hpEmb : MeasurableEmbedding p := measurableEmbedding_cylinder_integral_param n
  have hpMP : MeasurePreserving p μ μC :=
    ⟨hpEmb.measurable, map_cylinder_surface_product_Icc_eq_native_unitCylinder hn a b⟩
  have hu : Integrable u μC := by
    rw [← hpMP.map_eq]
    exact hpEmb.integrable_map_iff.mpr (hf.congr hparam.symm)
  have hC : MeasurableSet C := (isClosed_native_cylinder_surface_Icc n a b).measurableSet
  have hSubEmb := MeasurableEmbedding.subtype_coe hC
  have hmap : Measure.map (Subtype.val : C → Domain (n + 1)) σC = μC := by
    simpa only [Subtype.range_coe] using
      (Isometry.map_euclideanHausdorffMeasure (d := n)
        (isometry_subtype_coe : Isometry (Subtype.val : C → Domain (n + 1))))
  have hSubMP : MeasurePreserving (Subtype.val : C → Domain (n + 1)) σC μC :=
    ⟨measurable_subtype_coe, hmap⟩
  have huv : u ∘ (Subtype.val : C → Domain (n + 1)) = v := by
    funext y
    exact dif_pos y.property
  have hv : Integrable v σC := by
    rw [← hmap] at hu
    have h := hSubEmb.integrable_map_iff.mp hu
    rwa [huv] at h
  refine ⟨hv, ?_⟩
  calc
    (∫ y : C, v y ∂σC) = ∫ y : C, u y.val ∂σC := by
      exact integral_congr_ae (Eventually.of_forall fun y => (congrFun huv y).symm)
    _ = ∫ y, u y ∂μC := hSubMP.integral_comp hSubEmb u
    _ = ∫ z, u (p z) ∂μ := (hpMP.integral_comp hpEmb u).symm
    _ = ∫ z, f z ∂μ := integral_congr_ae hparam

end StratificationTheory
