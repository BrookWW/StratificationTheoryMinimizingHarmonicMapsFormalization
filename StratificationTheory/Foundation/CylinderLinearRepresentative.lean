module

public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.ContinuousMap.Basic
import HarmonicMaps.Analysis.VariableMollificationL2

/-!
# The continuous L2 curve of affine cylinder interpolation

Affine interpolation of two actual native sphere L2 maps gives one continuous
curve of L2 classes. At every time its class is the class of the literal raw
slice. The endpoint classes and squared increment norms are exact.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped Topology ENNReal

namespace StratificationTheory

/-- The squared distance between two actual native sphere L2 classes equals
the native integral of their pointwise squared discrepancy. -/
theorem sphereL2_class_discrepancy_eq_integral {n q : ℕ}
    {u v : sphere (0 : Domain n) 1 → Ambient q}
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))) :
    ‖hv.toLp v - hu.toLp u‖ ^ 2 =
      ∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
        ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  rw [← hv.toLp_sub hu, Lp.norm_toLp,
    ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hv.sub hu)]
  rfl

/-- Two actual native sphere L2 maps have one explicit affine continuous L2
representative on the closed interval. Its literal slice classes, endpoint
classes, and squared increments are all identified exactly. This statement
uses angular L2 data alone and does not require a Sobolev trace construction. -/
theorem exists_cylinder_linear_L2_representative {n q : ℕ}
    {a b : ℝ} (hab : a < b) {u v : sphere (0 : Domain n) 1 → Ambient q}
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ t : Icc a b, H t = (1 - ((t : ℝ) - a) / (b - a)) • hu.toLp u +
        (((t : ℝ) - a) / (b - a)) • hv.toLp v) ∧
      (∀ t : Icc a b,
        ∃ ht : MemLp (fun θ => (1 - ((t : ℝ) - a) / (b - a)) • u θ +
            (((t : ℝ) - a) / (b - a)) • v θ) 2 σ,
          H t = ht.toLp (fun θ => (1 - ((t : ℝ) - a) / (b - a)) • u θ +
            (((t : ℝ) - a) / (b - a)) • v θ)) ∧
      H ⟨a, le_rfl, hab.le⟩ = hu.toLp u ∧
      H ⟨b, hab.le, le_rfl⟩ = hv.toLp v ∧
      (∀ s t : Icc a b, ‖H t - H s‖ ^ 2 =
        (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 * ‖hv.toLp v - hu.toLp u‖ ^ 2) ∧
      ∀ s t : Icc a b, ‖H t - H s‖ ^ 2 =
        (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 *
          ∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2 ∂σ := by
  intro σ
  let U : Lp (Ambient q) 2 σ := hu.toLp u
  let V : Lp (Ambient q) 2 σ := hv.toLp v
  let α : Icc a b → ℝ := fun t => ((t : ℝ) - a) / (b - a)
  have hα : Continuous α :=
    (continuous_subtype_val.sub continuous_const).div_const (b - a)
  let H : C(Icc a b, Lp (Ambient q) 2 σ) :=
    ⟨fun t => (1 - α t) • U + α t • V,
      ((continuous_const.sub hα).smul continuous_const).add (hα.smul continuous_const)⟩
  have hraw (t : Icc a b) :
      ∃ ht : MemLp (fun θ => (1 - ((t : ℝ) - a) / (b - a)) • u θ +
          (((t : ℝ) - a) / (b - a)) • v θ) 2 σ,
        H t = ht.toLp (fun θ => (1 - ((t : ℝ) - a) / (b - a)) • u θ +
          (((t : ℝ) - a) / (b - a)) • v θ) := by
    have ht := (hu.const_smul (1 - α t)).add (hv.const_smul (α t))
    refine ⟨ht, ?_⟩
    change (1 - α t) • U + α t • V = ht.toLp _
    rw [(hu.const_smul (1 - α t)).toLp_add (hv.const_smul (α t)),
      MemLp.toLp_const_smul, MemLp.toLp_const_smul]
  have hinc (s t : Icc a b) :
      H t - H s = (((t : ℝ) - (s : ℝ)) / (b - a)) • (V - U) := by
    have hcoef : α t - α s = ((t : ℝ) - (s : ℝ)) / (b - a) := by
      dsimp only [α]
      ring
    change ((1 - α t) • U + α t • V) - ((1 - α s) • U + α s • V) = _
    rw [← hcoef]
    simp only [sub_smul, smul_sub, one_smul]
    abel
  have hnorm (s t : Icc a b) : ‖H t - H s‖ ^ 2 =
      (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 * ‖V - U‖ ^ 2 := by
    rw [hinc, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  refine ⟨H, fun _ => rfl, hraw, ?_, ?_, hnorm, ?_⟩
  · change (1 - (a - a) / (b - a)) • U + ((a - a) / (b - a)) • V = U
    simp only [sub_self, zero_div, sub_zero, one_smul, zero_smul, add_zero]
  · change (1 - (b - a) / (b - a)) • U + ((b - a) / (b - a)) • V = V
    simp only [div_self (sub_ne_zero.mpr (ne_of_gt hab)), sub_self, zero_smul,
      one_smul, zero_add]
  · intro s t
    rw [hnorm]
    exact congrArg (fun x : ℝ => (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 * x)
      (sphereL2_class_discrepancy_eq_integral hu hv)

end StratificationTheory
