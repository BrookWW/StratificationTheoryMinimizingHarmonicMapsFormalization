module

public import StratificationTheory.Foundation.CylinderParamMeasure
public import StratificationTheory.Foundation.CylinderLinearL2
public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Native L2 columns of a coherent affine cylinder field

A single angular full-measure set identifies all columns at every time.
Native measure transport then identifies the original field on the physical
cylinder before assigning L2 membership to each of its columns.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory

/-- A field with the displayed affine angular and constant time columns has
native cylinder L2 columns. This is a field-transport statement; it does not
assert that an arbitrary input field is a weak gradient. -/
theorem memLp_native_cylinder_columns_of_affine_formula {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (Gu Gv : Fin n → Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)))
    (D : Domain (n + 1) → Gradient (n + 1) q)
    (hD : ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t : ℝ,
        D ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
        Fin.addCases
          (fun i => (1 - (t - a) / (b - a)) • (Gu i) θ +
            ((t - a) / (b - a)) • (Gv i) θ)
          (fun _ => (b - a)⁻¹ • (v θ - u θ))) :
    ∀ i : Fin (n + 1), MemLp (fun c : unitCylinder n a b => D c.val i) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let F : unitCylinder n a b → Gradient (n + 1) q := fun c =>
    Fin.addCases
      (fun i => (1 - ((e c.val).2 0 - a) / (b - a)) • (Gu i) ⟨(e c.val).1, c.property.1⟩ +
        (((e c.val).2 0 - a) / (b - a)) • (Gv i) ⟨(e c.val).1, c.property.1⟩)
      (fun _ => (b - a)⁻¹ •
        (v ⟨(e c.val).1, c.property.1⟩ - u ⟨(e c.val).1, c.property.1⟩))
  have hDF : (fun c : unitCylinder n a b => D c.val) =ᵐ[Measure.euclideanHausdorffMeasure n] F := by
    apply ae_unitCylinder_of_ae_forall_time hn
    filter_upwards [hD] with θ hθ
    intro t
    dsimp only [F, e]
    simpa only [ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true] using hθ t.val
  have hFL (i : Fin (n + 1)) : MemLp (fun c => F c i) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [F, Fin.addCases_left] using
        memLp_two_unitCylinder_linearInterpolation hn hab (Lp.memLp (Gu j)) (Lp.memLp (Gv j))
    · let f : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p =>
        (b - a)⁻¹ • (v p.1 - u p.1)
      have hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))) :=
        ((hv.sub hu).const_smul (b - a)⁻¹).comp_fst _
      apply memLp_two_unitCylinder_of_param hn (fun c => F c _) f hf
      intro θ t
      dsimp only [F, f, e]
      simp only [Fin.addCases_right, ContinuousLinearEquiv.apply_symm_apply,
        PiLp.single_apply, ite_true]
  intro i
  exact (hFL i).ae_eq (hDF.symm.mono fun c hc => congrFun hc i)

end StratificationTheory
