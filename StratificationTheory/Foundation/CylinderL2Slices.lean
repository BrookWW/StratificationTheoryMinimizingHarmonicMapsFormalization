module

public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Native cylinder L2 slices

The actual Euclidean surface-product correspondence transports finite cylinder
L2 data to angular-time data. Fubini then gives native angular L2 slices and
the genuine integrability and exact disintegration of their squared norms.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

private theorem measurable_cylinder_surface_embedding (n : ℕ) :
    Measurable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let c := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n)) τ.symm).trans e.symm
  have heq : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) =
        c ∘ Prod.map Subtype.val id := by
    funext p
    change e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2) = e.symm (p.1.val, τ.symm p.2)
    congr 2
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  rw [heq]
  exact c.continuous.measurable.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

private theorem integral_cylinder_surface_pullback {n : ℕ} (hn : 0 < n)
    {a b : ℝ} {g : Domain (n + 1) → ℝ}
    (hg : Integrable g ((Measure.euclideanHausdorffMeasure n :
      Measure (Domain (n + 1))).restrict (unitCylinder n a b))) :
    (∫ p : sphere (0 : Domain n) 1 × ℝ,
      g ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
      ∂((Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b)))) =
      ∫ y in unitCylinder n a b, g y ∂Measure.euclideanHausdorffMeasure n := by
  have hm := map_cylinder_surface_product_Icc_eq_native_unitCylinder hn a b
  rw [← hm] at hg ⊢
  exact (integral_map (measurable_cylinder_surface_embedding n).aemeasurable
    hg.aestronglyMeasurable).symm

/-- Native finite cylinder L2 data pull back to the actual sphere-time product. -/
theorem memLp_two_cylinder_surface_pullback {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {u : Domain (n + 1) → E}
    (hu : MemLp u 2 ((Measure.euclideanHausdorffMeasure n :
      Measure (Domain (n + 1))).restrict (unitCylinder n a b))) :
    MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
      u ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))) := by
  rw [← map_cylinder_surface_product_Icc_eq_native_unitCylinder hn a b] at hu
  exact hu.comp_of_map (measurable_cylinder_surface_embedding n).aemeasurable

/-- Almost every closed-interval time slice of actual cylinder L2 data is in
native angular L2; no time derivative or endpoint trace is asserted. -/
theorem ae_memLp_two_cylinder_surface_slice {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {u : Domain (n + 1) → E}
    (hu : MemLp u 2 ((Measure.euclideanHausdorffMeasure n :
      Measure (Domain (n + 1))).restrict (unitCylinder n a b))) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      MemLp (fun θ : sphere (0 : Domain n) 1 =>
        u ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t))) 2
        (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)) := by
  letI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hp := memLp_two_cylinder_surface_pullback hn hu
  have hsq := hp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  filter_upwards [hp.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with t hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

/-- The actual squared slice norms are integrable and disintegrate the native
cylinder L2 energy exactly, including null or reversed time intervals. -/
theorem integrable_cylinder_slice_energy_and_integral {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {u : Domain (n + 1) → E}
    (hu : MemLp u 2 ((Measure.euclideanHausdorffMeasure n :
      Measure (Domain (n + 1))).restrict (unitCylinder n a b))) :
    Integrable (fun t : ℝ => ∫ θ : sphere (0 : Domain n) 1,
      ‖u ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) t))‖ ^ 2
        ∂Measure.euclideanHausdorffMeasure (n - 1)) (volume.restrict (Icc a b)) ∧
    (∫ t in Icc a b, ∫ θ : sphere (0 : Domain n) 1,
      ‖u ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) t))‖ ^ 2
        ∂Measure.euclideanHausdorffMeasure (n - 1)) =
      ∫ y in unitCylinder n a b, ‖u y‖ ^ 2 ∂Measure.euclideanHausdorffMeasure n := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  let μ := σ.prod (volume.restrict (Icc a b))
  let f := fun p : sphere (0 : Domain n) 1 × ℝ =>
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
      (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)
  have hp : MemLp (u ∘ f) 2 μ := memLp_two_cylinder_surface_pullback hn hu
  have hsq : Integrable (fun p => ‖u (f p)‖ ^ 2) μ :=
    hp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  exact ⟨hsq.integral_prod_right, (integral_prod_symm _ hsq).symm.trans
    (integral_cylinder_surface_pullback hn
      (hu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)))⟩

end StratificationTheory
