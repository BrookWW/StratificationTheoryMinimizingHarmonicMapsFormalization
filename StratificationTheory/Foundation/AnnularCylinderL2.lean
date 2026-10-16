module

public import StratificationTheory.Foundation.AnnularCylinderMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Native cylinder L2 data as actual annular volume data

The exact positive annular coordinate map and its bounded Jacobian transport
original functions, their L2 membership and their squared-norm integrals.
This is a measure statement; it does not prescribe a weak gradient.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal
namespace StratificationTheory

/-- Native unweighted sphere-time L2 of the original pullback gives actual
annular L2 and the upper-Jacobian squared-norm bound for the same function. -/
theorem memLp_two_annulus_of_cylinder_pullback {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {s a b : ℝ}
    (hs : 0 < s) (ha : -1 < a) (hab : a < b) (f : Domain n → E)
    (hf : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
      f ((s * (1 + p.2)) • p.1.val)) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Ioo a b)))) :
    MemLp f 2 (volume.restrict {x : Domain n |
      s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}) ∧
    (∫ x in {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}, ‖f x‖ ^ 2) ≤
      (s * (s * (1 + b)) ^ (n - 1)) *
        ∫ p : sphere (0 : Domain n) 1 × ℝ, ‖f ((s * (1 + p.2)) • p.1.val)‖ ^ 2
          ∂(Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
            (volume.restrict (Ioo a b)) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := volume.comap (Subtype.val : Ioo a b → ℝ)
  let μ := σ.prod ν
  let J : Ioo a b → ℝ≥0∞ := fun t => ENNReal.ofReal (s * (s * (1 + t.val)) ^ (n - 1))
  let C : ℝ := s * (s * (1 + b)) ^ (n - 1)
  let F : sphere (0 : Domain n) 1 × Ioo a b → Domain n := fun p =>
    (s * (1 + p.2.val)) • p.1.val
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite ν :=
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ))).sigmaFinite
  have hR : 0 < s * (1 + b) := mul_pos hs (by linarith only [ha, hab])
  have hC : 0 < C := mul_pos hs (pow_pos hR _)
  have hJ : Measurable J := by fun_prop
  have hparam := (MeasurePreserving.id σ).prod
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ)))
  have hp : MemLp (fun p => f (F p)) 2 μ := hf.comp_measurePreserving hparam
  have hbound : σ.prod (ν.withDensity J) ≤ ENNReal.ofReal C • μ := by
    rw [prod_withDensity_right hJ]
    conv_rhs => rw [← withDensity_const]
    apply withDensity_mono
    apply ae_of_all
    intro p
    apply ENNReal.ofReal_le_ofReal
    have hlo : 0 ≤ s * (1 + p.2.val) :=
      (mul_pos hs (by linarith only [ha, p.2.property.1])).le
    have hhi : s * (1 + p.2.val) ≤ s * (1 + b) :=
      mul_le_mul_of_nonneg_left (add_le_add_right p.2.property.2.le 1) hs.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo hhi (n - 1)) hs.le
  have hpC : MemLp (fun p => f (F p)) 2 (ENNReal.ofReal C • μ) :=
    hp.smul_measure ENNReal.ofReal_ne_top
  have hpJ : MemLp (fun p => f (F p)) 2 (σ.prod (ν.withDensity J)) :=
    hpC.mono_measure hbound
  have hm := measurePreserving_annular_cylinder_param (b := b) hn hs ha
  have he := measurableEmbedding_annular_cylinder_param (n := n) (b := b) hs ha
  have hfA : MemLp f 2 (volume.restrict {x : Domain n |
      s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}) := by
    rw [← hm.map_eq]
    exact he.memLp_map_measure_iff.mpr hpJ
  refine ⟨hfA, ?_⟩
  calc
    _ = ∫ p, ‖f (F p)‖ ^ 2 ∂σ.prod (ν.withDensity J) :=
      (hm.integral_comp he (fun x => ‖f x‖ ^ 2)).symm
    _ ≤ ∫ p, ‖f (F p)‖ ^ 2 ∂ENNReal.ofReal C • μ :=
      integral_mono_measure hbound (ae_of_all _ fun p => sq_nonneg _)
        (hpC.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    _ = C * ∫ p, ‖f (F p)‖ ^ 2 ∂μ := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul]
    _ = _ := by
      congr 1
      exact hparam.integral_comp
        (MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtype_coe measurableSet_Ioo))
        (fun p : sphere (0 : Domain n) 1 × ℝ => ‖f ((s * (1 + p.2)) • p.1.val)‖ ^ 2)

end StratificationTheory
