module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.L2Space
import HarmonicMaps.Analysis.VariableMollificationL2
import StratificationTheory.Foundation.RealReciprocalMeasure

/-!
# Continuous traces along reciprocal normal parameters

Endpoint continuity controls the actual parameters `1 - δ / t` uniformly
when time lies in a fixed positive compact interval.
-/

public section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StratificationTheory

/-- Small positive normal offsets give actual interior trace parameters
uniformly on every time interval bounded away from zero. -/
theorem conical_parameter_mem_Ioo {a b₀ δ t : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (hδ : 0 < δ) (hδcap : δ < (1 - a) * b₀) (ht : b₀ ≤ t) :
    1 - δ / t ∈ Ioo a 1 := by
  have htpos : 0 < t := hb₀.trans_le ht
  have hupper : δ / t < 1 - a := (div_lt_iff₀ htpos).mpr
    (hδcap.trans_le (mul_le_mul_of_nonneg_left ht (sub_pos.mpr ha).le))
  have hlower : 0 < δ / t := div_pos hδ htpos
  constructor <;> linarith

/-- Endpoint continuity produces a uniform small difference at every actual
reciprocal normal parameter, including both time endpoints. -/
theorem continuous_conical_parameter_eventually_uniform {E : Type*} [NormedAddCommGroup E]
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (H : C(Icc a 1, E)) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ t ∈ Icc b₀ b₁, 1 - δ / t ∈ Ioo a 1) ∧
      ∀ t ∈ Icc b₀ b₁, ∀ hz : 1 - δ / t ∈ Icc a 1,
        ‖H ⟨1 - δ / t, hz⟩ - H ⟨1, ha.le, le_rfl⟩‖ < ε := by
  intro ε hε
  let F : ℝ → E := IccExtend ha.le H
  have hF : Continuous F := H.continuous.Icc_extend'
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp hF.continuousAt ε hε
  have hcap : 0 < min ((1 - a) * b₀) (η * b₀) :=
    lt_min (mul_pos (sub_pos.mpr ha) hb₀) (mul_pos hη hb₀)
  filter_upwards [Ioo_mem_nhdsGT hcap] with δ hδ
  have hδcap : δ < (1 - a) * b₀ := hδ.2.trans_le (min_le_left _ _)
  have hδη : δ < η * b₀ := hδ.2.trans_le (min_le_right _ _)
  refine ⟨fun t ht => conical_parameter_mem_Ioo ha hb₀ hδ.1 hδcap ht.1, ?_⟩
  intro t ht hz
  have htpos : 0 < t := hb₀.trans_le ht.1
  have hdist : dist (1 - δ / t) 1 < η := by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (div_pos hδ.1 htpos)]
    exact (div_lt_iff₀ htpos).mpr
      (hδη.trans_le (mul_le_mul_of_nonneg_left ht.1 hη.le))
  have h := hclose hdist
  rw [show F (1 - δ / t) = H ⟨1 - δ / t, hz⟩ from IccExtend_of_mem ha.le H hz,
    show F 1 = H ⟨1, ha.le, le_rfl⟩ from IccExtend_right ha.le H] at h
  simpa only [dist_eq_norm] using h

private theorem continuous_conical_parameter_weighted_integral {E : Type*}
    [NormedAddCommGroup E] {a b₀ b₁ : ℝ} (ha : a < 1)
    (H : C(Icc a 1, E)) (m : ℕ) :
    let F : ℝ → E := IccExtend ha.le H
    (∀ δ : ℝ, Integrable (fun t => t ^ m * ‖F (1 - δ / t) - H ⟨1, ha.le, le_rfl⟩‖ ^ 2)
      (volume.restrict (Icc b₀ b₁))) ∧
    Tendsto (fun δ : ℝ => ∫ t in Icc b₀ b₁,
      t ^ m * ‖F (1 - δ / t) - H ⟨1, ha.le, le_rfl⟩‖ ^ 2) (𝓝 0) (𝓝 0) := by
  intro F
  let c := H ⟨1, ha.le, le_rfl⟩
  have hF : Continuous F := H.continuous.Icc_extend'
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (H.continuous.sub continuous_const).continuousOn
  have hnorm (z : ℝ) : ‖F z - c‖ ≤ M := hM (projIcc a 1 ha.le z) (mem_univ _)
  let ν := (volume : Measure ℝ).restrict (Icc b₀ b₁)
  have hboundI : Integrable (fun t : ℝ => |t| ^ m * M ^ 2) ν :=
    ((continuous_id.abs.pow m).mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hmeas (δ : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => t ^ m * ‖F (1 - δ / t) - c‖ ^ 2) ν := by
    have hg : Measurable (fun t : ℝ => 1 - δ / t) :=
      measurable_const.sub (measurable_const.div measurable_id)
    exact ((measurable_id.pow_const m).mul
      (((hF.sub continuous_const).norm.measurable.comp hg).pow_const 2)).aestronglyMeasurable
  have hbound (δ : ℝ) : ∀ᵐ t ∂ν,
      ‖t ^ m * ‖F (1 - δ / t) - c‖ ^ 2‖ ≤ |t| ^ m * M ^ 2 := by
    apply Eventually.of_forall
    intro t
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm _) 2)
      (pow_nonneg (abs_nonneg _) m)
  have hInt (δ : ℝ) : Integrable
      (fun t : ℝ => t ^ m * ‖F (1 - δ / t) - c‖ ^ 2) ν :=
    hboundI.mono' (hmeas δ) (hbound δ)
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun δ : ℝ =>
      t ^ m * ‖F (1 - δ / t) - c‖ ^ 2) (𝓝 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hg : Tendsto (fun δ : ℝ => 1 - δ / t) (𝓝 0) (𝓝 1) := by
      have hz : Tendsto (fun δ : ℝ => δ / t) (𝓝 (0 : ℝ)) (𝓝 (0 / t)) :=
        tendsto_id.div_const t
      have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
      simpa only [zero_div, sub_zero] using hc.sub hz
    have hc : F 1 = c := IccExtend_right ha.le H
    have hh := (((hF.tendsto 1).comp hg).sub_const c).norm.pow 2
    simpa only [Function.comp_apply, hc, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
      using hh.const_mul (t ^ m)
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => |t| ^ m * M ^ 2) (Eventually.of_forall hmeas)
    (Eventually.of_forall hbound) hboundI hlim
  exact ⟨hInt, by simpa only [integral_zero] using hconv⟩

/-- Every actual time representative of the reciprocal-parameter trace has
finite L2 difference and a weighted square integral tending uniformly to zero.
The representative hypothesis only identifies its original point values. -/
theorem continuous_conical_parameter_eventually_L2 {E : Type*} [NormedAddCommGroup E]
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (H : C(Icc a 1, E)) (m : ℕ) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ t ∈ Icc b₀ b₁, 1 - δ / t ∈ Ioo a 1) ∧
      ∀ u : ℝ → E,
        (∀ t ∈ Icc b₀ b₁, ∀ hz : 1 - δ / t ∈ Icc a 1,
          u t = H ⟨1 - δ / t, hz⟩) →
        MemLp (fun t => u t - H ⟨1, ha.le, le_rfl⟩) 2
          (volume.restrict (Icc b₀ b₁)) ∧
        Integrable (fun t => t ^ m * ‖u t - H ⟨1, ha.le, le_rfl⟩‖ ^ 2)
          (volume.restrict (Icc b₀ b₁)) ∧
        (∫ t in Icc b₀ b₁, t ^ m * ‖u t - H ⟨1, ha.le, le_rfl⟩‖ ^ 2) < ε := by
  intro ε hε
  let F : ℝ → E := IccExtend ha.le H
  let c := H ⟨1, ha.le, le_rfl⟩
  let ν := (volume : Measure ℝ).restrict (Icc b₀ b₁)
  have hF : Continuous F := H.continuous.Icc_extend'
  have hM := continuous_conical_parameter_weighted_integral (b₀ := b₀) (b₁ := b₁) ha H m
  have hZero := continuous_conical_parameter_weighted_integral (b₀ := b₀) (b₁ := b₁) ha H 0
  have hInt0 (δ : ℝ) : Integrable (fun t => ‖F (1 - δ / t) - c‖ ^ 2) ν := by
    simpa only [pow_zero, one_mul] using hZero.1 δ
  have hMem (δ : ℝ) : MemLp (fun t => F (1 - δ / t) - c) 2 ν := by
    have hg : Measurable (fun t : ℝ => 1 - δ / t) :=
      measurable_const.sub (measurable_const.div measurable_id)
    have hG0 : AEStronglyMeasurable (fun t : ℝ => F (1 - δ / t)) ν :=
      (hF.stronglyMeasurable.comp_measurable hg).aestronglyMeasurable
    have hG : AEStronglyMeasurable (fun t : ℝ => F (1 - δ / t) - c) ν :=
      hG0.sub aestronglyMeasurable_const
    exact (memLp_two_iff_integrable_sq_norm hG).mpr (hInt0 δ)
  have hSmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ t in Icc b₀ b₁, t ^ m * ‖F (1 - δ / t) - c‖ ^ 2) < ε :=
    (hM.2.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hε)
  filter_upwards [continuous_conical_parameter_eventually_uniform ha hb₀ H 1 zero_lt_one,
    hSmall] with δ hδ hδsmall
  refine ⟨hδ.1, ?_⟩
  intro u hu
  have heq : (fun t => F (1 - δ / t) - c) =ᵐ[ν] (fun t => u t - c) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hz := hδ.1 t ht
    rw [show F (1 - δ / t) = H ⟨1 - δ / t, hz.1.le, hz.2.le⟩ from
      IccExtend_of_mem ha.le H ⟨hz.1.le, hz.2.le⟩, hu t ht ⟨hz.1.le, hz.2.le⟩]
  have hweighted : (fun t => t ^ m * ‖F (1 - δ / t) - c‖ ^ 2) =ᵐ[ν]
      (fun t => t ^ m * ‖u t - c‖ ^ 2) := by
    filter_upwards [heq] with t ht
    rw [ht]
  exact ⟨(hMem δ).ae_eq heq, (hM.1 δ).congr hweighted,
    (integral_congr_ae hweighted).symm ▸ hδsmall⟩

private theorem conical_raw_rows {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (σ : Measure X) [IsFiniteMeasure σ] {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (H : C(Icc a 1, Lp E 2 σ)) {f : X × ℝ → E}
    (hf : AEStronglyMeasurable f (σ.prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 σ,
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z)))
    {g : X → E} (hg : MemLp g 2 σ)
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g)
    {δ : ℝ} (hδ : 0 < δ) (hδcap : δ < (1 - a) * b₀) :
    let ν := (volume : Measure ℝ).restrict (Icc b₀ b₁)
    let R : X × ℝ → E := fun p => f (p.1, 1 - δ / p.2) - g p.1
    AEStronglyMeasurable R (σ.prod ν) ∧
    ∀ᵐ t ∂ν,
      MemLp (fun x => R (x,t)) 2 σ ∧
      (∫ x, ‖R (x,t)‖ ^ 2 ∂σ) =
        ‖IccExtend ha.le H (1 - δ / t) - H ⟨1, ha.le, le_rfl⟩‖ ^ 2 := by
  intro ν R
  have hQ : Measure.QuasiMeasurePreserving (fun t : ℝ => 1 - δ / t)
      ν (volume.restrict (Ioo a 1)) :=
    (quasiMeasurePreserving_one_sub_div hδ.ne').restrict
      (fun t ht => conical_parameter_mem_Ioo ha hb₀ hδ hδcap ht.1)
  have hProdQ := QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id σ) hQ
  have hF : AEStronglyMeasurable (fun p : X × ℝ => f (p.1, 1 - δ / p.2)) (σ.prod ν) :=
    hf.comp_quasiMeasurePreserving hProdQ
  have hG : AEStronglyMeasurable (fun p : X × ℝ => g p.1) (σ.prod ν) :=
    hg.aestronglyMeasurable.comp_fst
  refine ⟨hF.sub hG, ?_⟩
  have hRaw := (quasiMeasurePreserving_one_sub_div hδ.ne').ae hSlices
  filter_upwards [hRaw.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Icc] with t ht htI
  have hz := conical_parameter_mem_Ioo ha hb₀ hδ hδcap htI.1
  obtain ⟨hs, hEq⟩ := ht hz
  have hsub : MemLp (fun x => f (x,1 - δ / t) - g x) 2 σ :=
    (hs.sub hg).ae_eq (Eventually.of_forall fun _ => rfl)
  have hClass : IccExtend ha.le H (1 - δ / t) - H ⟨1, ha.le, le_rfl⟩ =
      (hs.sub hg).toLp (fun x => f (x,1 - δ / t) - g x) := by
    rw [IccExtend_of_mem ha.le H ⟨hz.1.le, hz.2.le⟩, hEq, hEnd, ← hs.toLp_sub hg]
    rfl
  refine ⟨hsub, ?_⟩
  rw [hClass, Lp.norm_toLp]
  exact HarmonicMaps.integral_norm_sq_eq_eLpNorm_two_toReal_sq hsub

private theorem conical_raw_weighted_data {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (σ : Measure X) [IsFiniteMeasure σ]
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (H : C(Icc a 1, Lp E 2 σ)) {f : X × ℝ → E}
    (hf : AEStronglyMeasurable f (σ.prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 σ,
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z)))
    {g : X → E} (hg : MemLp g 2 σ)
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g)
    {δ : ℝ} (hδ : 0 < δ) (hδcap : δ < (1 - a) * b₀) (m : ℕ) :
    let ν := (volume : Measure ℝ).restrict (Icc b₀ b₁)
    let R : X × ℝ → E := fun p => f (p.1, 1 - δ / p.2) - g p.1
    MemLp R 2 (σ.prod ν) ∧
    Integrable (fun p : X × ℝ => p.2 ^ m * ‖R p‖ ^ 2) (σ.prod ν) ∧
    (∫ p : X × ℝ, p.2 ^ m * ‖R p‖ ^ 2 ∂σ.prod ν) =
      ∫ t in Icc b₀ b₁, t ^ m *
        ‖IccExtend ha.le H (1 - δ / t) - H ⟨1, ha.le, le_rfl⟩‖ ^ 2 := by
  intro ν R
  have hRows := conical_raw_rows (b₁ := b₁) σ ha hb₀ H hf hSlices hg hEnd hδ hδcap
  let F : ℝ → Lp E 2 σ := IccExtend ha.le H
  let c := H ⟨1, ha.le, le_rfl⟩
  have hweighted (k : ℕ) : Integrable
      (fun p : X × ℝ => p.2 ^ k * ‖R p‖ ^ 2) (σ.prod ν) := by
    have hAS : AEStronglyMeasurable
        (fun p : X × ℝ => p.2 ^ k * ‖R p‖ ^ 2) (σ.prod ν) :=
      (measurable_snd.pow_const k).aestronglyMeasurable.mul (hRows.1.norm.pow 2)
    apply (integrable_prod_iff' hAS).mpr
    constructor
    · filter_upwards [hRows.2] with t ht
      exact (ht.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul (t ^ k)
    · have hNorm : (fun t => ∫ x, ‖t ^ k * ‖R (x,t)‖ ^ 2‖ ∂σ) =ᵐ[ν]
          (fun t => t ^ k * ‖F (1 - δ / t) - c‖ ^ 2) := by
        filter_upwards [hRows.2, ae_restrict_mem measurableSet_Icc] with t ht htI
        have htpos : 0 ≤ t := (hb₀.trans_le htI.1).le
        simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg htpos k) (sq_nonneg _))]
        rw [integral_const_mul, ht.2]
      exact (continuous_conical_parameter_weighted_integral
        (b₀ := b₀) (b₁ := b₁) ha H k).1 δ |>.congr hNorm.symm
  have hSq : Integrable (fun p : X × ℝ => ‖R p‖ ^ 2) (σ.prod ν) := by
    simpa only [pow_zero, one_mul] using hweighted 0
  refine ⟨(memLp_two_iff_integrable_sq_norm hRows.1).mpr hSq, hweighted m, ?_⟩
  rw [integral_prod_symm _ (hweighted m)]
  apply integral_congr_ae
  filter_upwards [hRows.2] with t ht
  rw [integral_const_mul, ht.2]

private theorem conical_tendsto_eLpNorm_two_zero {ι X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {l : Filter ι} {f : ι → X → E}
    (hf : ∀ᶠ i in l, MemLp (f i) 2 μ)
    (hlim : Tendsto (fun i => ∫ x, ‖f i x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0) := by
  have ht := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hlim)
  have heq : ∀ᶠ i in l, ENNReal.ofReal (Real.sqrt (∫ x, ‖f i x‖ ^ 2 ∂μ)) =
      eLpNorm (f i) 2 μ := by
    filter_upwards [hf] with i hi
    rw [Real.sqrt_eq_rpow]
    symm
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using
      hi.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have ht' : Tendsto (fun i => ENNReal.ofReal (Real.sqrt (∫ x, ‖f i x‖ ^ 2 ∂μ))) l (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero] using ht
  exact ht'.congr' heq

/-- Original jointly measurable slices representing a continuous L2 curve
converge along the actual reciprocal normal parameters in product L2.
Every natural time-power weight has its actual square-integral limit. -/
theorem tendsto_raw_conical_parameter_L2 {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (σ : Measure X) [IsFiniteMeasure σ]
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (H : C(Icc a 1, Lp E 2 σ)) {f : X × ℝ → E}
    (hf : AEStronglyMeasurable f (σ.prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 σ,
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z)))
    {g : X → E} (hg : MemLp g 2 σ)
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g) :
    let ν := (volume : Measure ℝ).restrict (Icc b₀ b₁)
    let R : ℝ → X × ℝ → E := fun δ p => f (p.1, 1 - δ / p.2) - g p.1
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 (σ.prod ν)) ∧
    (∀ m : ℕ,
      (∀ᶠ δ in 𝓝[>] (0 : ℝ),
        Integrable (fun p : X × ℝ => p.2 ^ m * ‖R δ p‖ ^ 2) (σ.prod ν)) ∧
      Tendsto (fun δ : ℝ => ∫ p : X × ℝ, p.2 ^ m * ‖R δ p‖ ^ 2 ∂σ.prod ν)
        (𝓝[>] 0) (𝓝 0)) ∧
    Tendsto (fun δ : ℝ => eLpNorm (R δ) 2 (σ.prod ν)) (𝓝[>] 0) (𝓝 0) := by
  intro ν R
  have hSmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < (1 - a) * b₀ :=
    Ioo_mem_nhdsGT (mul_pos (sub_pos.mpr ha) hb₀)
  have hMem : ∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 (σ.prod ν) := by
    filter_upwards [hSmall] with δ hδ
    exact (conical_raw_weighted_data (b₁ := b₁) σ ha hb₀ H hf hSlices hg hEnd hδ.1 hδ.2 0).1
  have hIntegral (m : ℕ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Integrable (fun p : X × ℝ => p.2 ^ m * ‖R δ p‖ ^ 2) (σ.prod ν) := by
    filter_upwards [hSmall] with δ hδ
    exact (conical_raw_weighted_data (b₁ := b₁) σ ha hb₀ H hf hSlices hg hEnd hδ.1 hδ.2 m).2.1
  have hLimit (m : ℕ) : Tendsto (fun δ : ℝ =>
      ∫ p : X × ℝ, p.2 ^ m * ‖R δ p‖ ^ 2 ∂σ.prod ν) (𝓝[>] 0) (𝓝 0) := by
    have ht := (continuous_conical_parameter_weighted_integral
      (b₀ := b₀) (b₁ := b₁) ha H m).2.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    apply ht.congr'
    filter_upwards [hSmall] with δ hδ
    exact (conical_raw_weighted_data (b₁ := b₁) σ ha hb₀ H hf hSlices hg hEnd hδ.1 hδ.2 m).2.2.symm
  refine ⟨hMem, fun m => ⟨hIntegral m, hLimit m⟩, ?_⟩
  apply conical_tendsto_eLpNorm_two_zero hMem
  simpa only [pow_zero, one_mul] using hLimit 0

end StratificationTheory
