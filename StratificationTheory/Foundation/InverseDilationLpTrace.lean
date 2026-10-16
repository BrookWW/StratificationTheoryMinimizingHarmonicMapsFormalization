module

public import HarmonicMaps.Analysis.L2AffineContinuity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import StratificationTheory.Foundation.RadialTraceCompatibility

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- The original inverse-dilation L2 classes form one continuous curve on the
entire positive-radius carrier. -/
theorem exists_continuous_inverse_dilation_L2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} (hf : MemLp f 2 volume) :
    ∃ H : C({r : ℝ // 0 < r}, Lp E 2 (volume : Measure (Domain n))),
      ∀ r : {r : ℝ // 0 < r},
        ∃ hr : MemLp (fun x : Domain n => f (r.val⁻¹ • x)) 2 volume,
          H r = hr.toLp (fun x : Domain n => f (r.val⁻¹ • x)) := by
  have hmem (r : {r : ℝ // 0 < r}) : MemLp (fun x : Domain n => f (r.val⁻¹ • x)) 2 volume := by
    simpa only [zero_add, sub_zero] using
      memLp_comp_centeredDilation hf (0 : Domain n) (inv_ne_zero r.property.ne')
  let H : {r : ℝ // 0 < r} → Lp E 2 (volume : Measure (Domain n)) :=
    fun r => (hmem r).toLp (fun x : Domain n => f (r.val⁻¹ • x))
  have hcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro r₀
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun r : {r : ℝ // 0 < r} => fun x : Domain n => f (r.val⁻¹ • x))
      hmem (fun x : Domain n => f (r₀.val⁻¹ • x)) (hmem r₀)).mpr
    change Tendsto (fun r : {r : ℝ // 0 < r} =>
      eLpNorm (fun x : Domain n => f (r.val⁻¹ • x) - f (r₀.val⁻¹ • x)) 2 volume)
      (𝓝 r₀) (𝓝 0)
    have ht : Tendsto (fun r : {r : ℝ // 0 < r} => r₀.val / r.val) (𝓝 r₀) (𝓝 1) := by
      have hc : Continuous (fun r : {r : ℝ // 0 < r} => r₀.val / r.val) :=
        continuous_const.div continuous_subtype_val (fun r => r.property.ne')
      simpa only [div_self r₀.property.ne'] using hc.tendsto r₀
    have h := (tendsto_eLpNorm_centeredDilation_sub (hmem r₀) (0 : Domain n)).comp ht
    simpa only [Function.comp_def, Pi.sub_apply, zero_add, sub_zero, smul_smul, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ r₀.property.ne', one_mul] using h
  exact ⟨⟨H, hcont⟩, fun r => ⟨hmem r, rfl⟩⟩

/-- A geometric collar inclusion gives a continuous L2 trace on every fixed
measurable subface. Both the original endpoint class and whole-curve
uniqueness come from the actual inverse-dilation slices. -/
theorem exists_inverse_dilation_L2_trace_on_subset {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S U : Set (Domain n)} (hS : MeasurableSet S) (hU : MeasurableSet U)
    {f : Domain n → E} (hf : MemLp f 2 (volume.restrict S))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hcontain : ∀ r : Icc ρ 1, ∀ x ∈ U, r.val⁻¹ • x ∈ S) :
    ∃ H : C(Icc ρ 1, Lp E 2 (volume.restrict U)),
      (∀ r : Icc ρ 1,
        ∃ hr : MemLp (fun x : Domain n => f (r.val⁻¹ • x)) 2 (volume.restrict U),
          H r = hr.toLp (fun x : Domain n => f (r.val⁻¹ • x))) ∧
      (∃ hFU : MemLp f 2 (volume.restrict U), H ⟨1, hρ1.le, le_rfl⟩ = hFU.toLp f) ∧
      ∀ K : C(Icc ρ 1, Lp E 2 (volume.restrict U)),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo ρ 1,
          ∃ hslice : MemLp (fun x : Domain n => f (r⁻¹ • x)) 2 (volume.restrict U),
            K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x : Domain n => f (r⁻¹ • x))) → K = H := by
  let g := S.indicator f
  have hg : MemLp g 2 volume := memLp_zeroExtension hS hf
  obtain ⟨HG, hHG⟩ := exists_continuous_inverse_dilation_L2 hg
  let τ : C(Icc ρ 1, {r : ℝ // 0 < r}) :=
    ⟨fun r => ⟨r.val, hρ.trans_le r.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  have hmemG (r : Icc ρ 1) : MemLp (fun x : Domain n => g (r.val⁻¹ • x)) 2 volume := by
    simpa only [zero_add, sub_zero] using memLp_comp_centeredDilation hg
      (0 : Domain n) (inv_ne_zero (hρ.trans_le r.property.1).ne')
  have hraw (r : Icc ρ 1) : (fun x : Domain n => g (r.val⁻¹ • x)) =ᵐ[volume.restrict U]
      (fun x : Domain n => f (r.val⁻¹ • x)) := by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact Set.indicator_of_mem (hcontain r x hx) f
  have hmem (r : Icc ρ 1) : MemLp (fun x : Domain n => f (r.val⁻¹ • x)) 2
      (volume.restrict U) := ((hmemG r).mono_measure Measure.restrict_le_self).ae_eq (hraw r)
  let Hfun : Icc ρ 1 → Lp E 2 (volume.restrict U) :=
    fun r => (hmem r).toLp (fun x : Domain n => f (r.val⁻¹ • x))
  have hGpoint (r : Icc ρ 1) : HG (τ r) =
      (hmemG r).toLp (fun x : Domain n => g (r.val⁻¹ • x)) := by
    obtain ⟨hL, hEq⟩ := hHG (τ r)
    exact hEq
  have hcont : Continuous Hfun := by
    apply continuous_iff_continuousAt.mpr
    intro r₀
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun r : Icc ρ 1 => fun x : Domain n => f (r.val⁻¹ • x)) hmem
      (fun x : Domain n => f (r₀.val⁻¹ • x)) (hmem r₀)).mpr
    have hlimLp := ((HG.continuous.comp τ.continuous).tendsto r₀)
    simp only [Function.comp_def, hGpoint] at hlimLp
    have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun r : Icc ρ 1 => fun x : Domain n => g (r.val⁻¹ • x)) hmemG
      (fun x : Domain n => g (r₀.val⁻¹ • x)) (hmemG r₀)).mp hlimLp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le)
    intro r
    calc
      _ = eLpNorm ((fun x : Domain n => g (r.val⁻¹ • x)) -
          (fun x : Domain n => g (r₀.val⁻¹ • x))) 2 (volume.restrict U) :=
        eLpNorm_congr_ae ((hraw r).sub (hraw r₀)).symm
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  let H : C(Icc ρ 1, Lp E 2 (volume.restrict U)) := ⟨Hfun, hcont⟩
  have hnorm (r : Icc ρ 1) : ∃ hr : MemLp (fun x : Domain n => f (r.val⁻¹ • x)) 2
      (volume.restrict U), H r = hr.toLp (fun x : Domain n => f (r.val⁻¹ • x)) := ⟨hmem r, rfl⟩
  refine ⟨H, hnorm, ?_, ?_⟩
  · obtain ⟨hL, hEq⟩ := hnorm ⟨1, hρ1.le, le_rfl⟩
    have hL' : MemLp f 2 (volume.restrict U) := by
      simpa only [inv_one, one_smul] using hL
    refine ⟨hL', hEq.trans ?_⟩
    exact hL.toLp_congr hL' (Eventually.of_forall fun x => by
      simp only [inv_one, one_smul])
  · intro K hK
    apply continuous_Lp_representatives_eq_of_ae_slices
      (f := fun p : Domain n × ℝ => f (p.2⁻¹ • p.1))
      (g := fun p : Domain n × ℝ => f (p.2⁻¹ • p.1)) hρ1 K H hK
      (Eventually.of_forall fun r hr => hnorm ⟨r, hr.1.le, hr.2.le⟩)
    exact Eventually.of_forall fun _ _ => EventuallyEq.rfl

/-- An original almost-everywhere property transfers to a contained fixed
subface under every nonzero inverse dilation, without measurability of the
value predicate. -/
theorem ae_inverse_dilation_property_on_subset {n : ℕ} {E : Type*}
    {S U : Set (Domain n)} (hS : MeasurableSet S) (hU : MeasurableSet U)
    (f : Domain n → E) (P : E → Prop) {t : ℝ} (ht : t ≠ 0)
    (hcontain : ∀ x ∈ U, t⁻¹ • x ∈ S)
    (hP : ∀ᵐ x ∂volume.restrict S, P (f x)) :
    ∀ᵐ x ∂volume.restrict U, P (f (t⁻¹ • x)) := by
  have hp := (ae_restrict_iff' hS).mp hP
  have hpull := (Measure.quasiMeasurePreserving_smul (volume : Measure (Domain n))
    (inv_ne_zero ht)).ae hp
  filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae hpull] with x hx hpx
  exact hpx (hcontain x hx)

end StratificationTheory
