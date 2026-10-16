module

public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import StratificationTheory.Foundation.AngularL2Membership
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul

/-!
# Energy of explicit affine cylinder fields

Affine interpolation of finite L2 field families has an integrable squared
norm on the native sphere-time product. Exact time-weight integrals give the
spatial coefficient one half of the interval length. The constant temporal
field has exactly the reciprocal-length discrepancy energy. The fields here
are specified algebraically; no identification with a Sobolev product
gradient is assumed or asserted.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory

private theorem affine_interval_weight_integrals {a b : ℝ} (hab : a < b) :
    (∫ t in Icc a b, (t - a) / (b - a)) = (b - a) / 2 ∧
    (∫ t in Icc a b, 1 - (t - a) / (b - a)) = (b - a) / 2 := by
  have hα : (∫ t in Icc a b, (t - a) / (b - a)) = (b - a) / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_div,
      intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => a)
        (continuous_id.intervalIntegrable a b)
        (continuous_const.intervalIntegrable a b),
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
    field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  refine ⟨hα, ?_⟩
  have hi : IntegrableOn (fun t : ℝ => (t - a) / (b - a)) (Icc a b) :=
    ((continuous_id.sub continuous_const).div_const (b - a)).continuousOn.integrableOn_Icc
  rw [integral_sub (integrable_const _) hi, hα, integral_const]
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  rw [hmass, smul_eq_mul]
  ring

private theorem norm_affine_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : 0 ≤ α) (hαone : α ≤ 1) (x y : E) :
    ‖(1 - α) • x + α • y‖ ^ 2 ≤ (1 - α) * ‖x‖ ^ 2 + α * ‖y‖ ^ 2 := by
  have hc : ConvexOn ℝ univ (fun z : E => ‖z‖ ^ 2) :=
    convexOn_univ_norm.pow (fun z _ => norm_nonneg z) 2
  simpa only [smul_eq_mul] using hc.2 (mem_univ x) (mem_univ y)
    (sub_nonneg.mpr hαone) hα (by ring : 1 - α + α = 1)

/-- An actual affine interpolation of two L2 fields has finite squared-norm
integral, bounded by one half of the interval length times the two energies. -/
theorem affine_field_integrable_energy_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) [SFinite μ]
    {a b : ℝ} (hab : a < b) {u v : X → E}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun p : X × ℝ =>
      ‖(1 - (p.2 - a) / (b - a)) • u p.1 + ((p.2 - a) / (b - a)) • v p.1‖ ^ 2)
        (μ.prod (volume.restrict (Icc a b))) ∧
    (∫ p : X × ℝ,
      ‖(1 - (p.2 - a) / (b - a)) • u p.1 + ((p.2 - a) / (b - a)) • v p.1‖ ^ 2
        ∂μ.prod (volume.restrict (Icc a b))) ≤
      ((b - a) / 2) * ((∫ x, ‖u x‖ ^ 2 ∂μ) + ∫ x, ‖v x‖ ^ 2 ∂μ) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let α : ℝ → ℝ := fun t => (t - a) / (b - a)
  let β : ℝ → ℝ := fun t => 1 - α t
  let f : X × ℝ → ℝ := fun p => ‖β p.2 • u p.1 + α p.2 • v p.1‖ ^ 2
  let B : X × ℝ → ℝ := fun p => ‖u p.1‖ ^ 2 * β p.2 + ‖v p.1‖ ^ 2 * α p.2
  have hα : Continuous α := (continuous_id.sub continuous_const).div_const (b - a)
  have hβ : Continuous β := continuous_const.sub hα
  have hαI : Integrable α ν := hα.continuousOn.integrableOn_Icc
  have hβI : Integrable β ν := hβ.continuousOn.integrableOn_Icc
  have hu2 := hu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hv2 := hv.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hBu : Integrable (fun p : X × ℝ => ‖u p.1‖ ^ 2 * β p.2) (μ.prod ν) := hu2.mul_prod hβI
  have hBv : Integrable (fun p : X × ℝ => ‖v p.1‖ ^ 2 * α p.2) (μ.prod ν) := hv2.mul_prod hαI
  have hBI : Integrable B (μ.prod ν) := hBu.add hBv
  have hfm : AEStronglyMeasurable f (μ.prod ν) :=
    (((hβ.measurable.comp measurable_snd).aestronglyMeasurable.smul
      (hu.comp_fst ν).aestronglyMeasurable).add
      ((hα.measurable.comp measurable_snd).aestronglyMeasurable.smul
        (hv.comp_fst ν).aestronglyMeasurable)).norm.pow 2
  have hbound : ∀ᵐ p ∂μ.prod ν, f p ≤ B p := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (measurableSet_Icc (a := a) (b := b)))] with p hp
    have hlo : 0 ≤ α p.2 := div_nonneg (sub_nonneg.mpr hp.1) (sub_pos.mpr hab).le
    have hhi : α p.2 ≤ 1 :=
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hp.2 a)
    simpa only [f, B, β, mul_comm] using norm_affine_sq_le hlo hhi (u p.1) (v p.1)
  have hfI : Integrable f (μ.prod ν) := hBI.mono' hfm (hbound.mono (fun p hp => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ f p from sq_nonneg _)] using hp))
  refine ⟨hfI, ?_⟩
  calc
    (∫ p, f p ∂μ.prod ν) ≤ ∫ p, B p ∂μ.prod ν := integral_mono_ae hfI hBI hbound
    _ = ((b - a) / 2) * ((∫ x, ‖u x‖ ^ 2 ∂μ) + ∫ x, ‖v x‖ ^ 2 ∂μ) := by
      rw [integral_add hBu hBv,
        integral_prod_mul (μ := μ) (ν := ν) (fun x => ‖u x‖ ^ 2) β,
        integral_prod_mul (μ := μ) (ν := ν) (fun x => ‖v x‖ ^ 2) α]
      dsimp only [α, β, ν]
      rw [(affine_interval_weight_integrals hab).1, (affine_interval_weight_integrals hab).2]
      ring

/-- The actual constant temporal difference field is square-integrable and
has exactly reciprocal-length discrepancy energy. -/
theorem constant_time_difference_integrable_energy {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) [SFinite μ]
    {a b : ℝ} (hab : a < b) {u v : X → E}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun p : X × ℝ => ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2)
      (μ.prod (volume.restrict (Icc a b))) ∧
    (∫ p : X × ℝ, ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2
      ∂μ.prod (volume.restrict (Icc a b))) =
      (b - a)⁻¹ * ∫ x, ‖v x - u x‖ ^ 2 ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have hbase : Integrable (fun x => ‖(b - a)⁻¹ • (v x - u x)‖ ^ 2) μ :=
    ((hv.sub hu).const_smul (b - a)⁻¹).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  refine ⟨hbase.comp_fst ν, ?_⟩
  rw [integral_fun_fst (μ := μ) (ν := ν)
    (fun x => ‖(b - a)⁻¹ • (v x - u x)‖ ^ 2)]
  have hmass : ν.real univ = b - a := by
    simp only [ν, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, hmass, smul_eq_mul]
  field_simp [sub_ne_zero.mpr (ne_of_gt hab)]

private theorem native_sphere_sFinite (n : ℕ) :
    SFinite (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) := by
  by_cases hn : 0 < n
  · haveI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) := by
      rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
      infer_instance
    infer_instance
  · have hn0 : n = 0 := by omega
    subst n
    letI : IsEmpty (sphere (0 : Domain 0) 1) := ⟨fun θ => by
      have hh := mem_sphere_zero_iff_norm.mp θ.property
      rw [Subsingleton.elim θ.val (0 : Domain 0), norm_zero] at hh
      norm_num at hh⟩
    infer_instance

/-- The explicit affine column fields together with the constant temporal
field have finite native sphere-time energy. The estimate uses the exact
spatial coefficient `L / 2` and temporal coefficient `L⁻¹`. -/
theorem native_linear_cylinder_field_energy {n q k : ℕ} {a b : ℝ} (hab : a < b)
    {u v : sphere (0 : Domain n) 1 → Ambient q}
    {Gu Gv : sphere (0 : Domain n) 1 → Fin k → Ambient q}
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hGu : ∀ i, MemLp (fun θ => Gu θ i) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hGv : ∀ i, MemLp (fun θ => Gv θ i) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Icc a b))
    Integrable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (∑ i : Fin k, ‖(1 - (p.2 - a) / (b - a)) • Gu p.1 i +
        ((p.2 - a) / (b - a)) • Gv p.1 i‖ ^ 2) +
        ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2) μ ∧
    Integrable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2) μ ∧
    (∫ p : sphere (0 : Domain n) 1 × ℝ,
      ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2 ∂μ) =
      (b - a)⁻¹ * (∫ θ, ‖v θ - u θ‖ ^ 2 ∂σ) ∧
    (∫ p : sphere (0 : Domain n) 1 × ℝ,
      (∑ i : Fin k, ‖(1 - (p.2 - a) / (b - a)) • Gu p.1 i +
        ((p.2 - a) / (b - a)) • Gv p.1 i‖ ^ 2) +
        ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2 ∂μ) ≤
      ((b - a) / 2) * (∫ θ, ∑ i : Fin k, (‖Gu θ i‖ ^ 2 + ‖Gv θ i‖ ^ 2) ∂σ) +
        (b - a)⁻¹ * (∫ θ, ‖v θ - u θ‖ ^ 2 ∂σ) := by
  intro σ μ
  letI : SFinite σ := native_sphere_sFinite n
  let S : Fin k → sphere (0 : Domain n) 1 × ℝ → ℝ := fun i p =>
    ‖(1 - (p.2 - a) / (b - a)) • Gu p.1 i + ((p.2 - a) / (b - a)) • Gv p.1 i‖ ^ 2
  have hS (i : Fin k) : Integrable (S i) μ ∧
      (∫ p, S i p ∂μ) ≤ ((b - a) / 2) *
        ((∫ θ, ‖Gu θ i‖ ^ 2 ∂σ) + ∫ θ, ‖Gv θ i‖ ^ 2 ∂σ) :=
    affine_field_integrable_energy_le σ hab
      (u := fun θ => Gu θ i) (v := fun θ => Gv θ i) (hGu i) (hGv i)
  have hT := constant_time_difference_integrable_energy σ hab hu hv
  have hSI : Integrable (fun p => ∑ i : Fin k, S i p) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hS i).1)
  have hEi (i : Fin k) : Integrable (fun θ => ‖Gu θ i‖ ^ 2 + ‖Gv θ i‖ ^ 2) σ :=
    ((hGu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).add
      ((hGv i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  refine ⟨hSI.add hT.1, hT.1, hT.2, ?_⟩
  rw [integral_add hSI hT.1, hT.2]
  refine add_le_add ?_ le_rfl
  rw [integral_finsetSum Finset.univ (fun i _ => (hS i).1),
    integral_finsetSum Finset.univ (fun i _ => hEi i), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_add ((hGu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    ((hGv i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))]
  exact (hS i).2

end StratificationTheory
