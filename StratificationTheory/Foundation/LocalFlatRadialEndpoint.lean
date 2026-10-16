module

public import StratificationTheory.Foundation.LpTwoMeasureRestriction
public import StratificationTheory.Foundation.InverseDilationLpTrace

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- A continuous full-base trace whose actual slices are inverse dilations
on a contained subface has the original endpoint class on that subface. -/
theorem continuous_flat_trace_endpoint_on_radial_subface {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S U : Set (Domain n)} (hS : MeasurableSet S) (hU : MeasurableSet U) (hUS : U ⊆ S)
    {a ρ : ℝ} (haρ : a ≤ ρ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f : Domain n → E) (hf : MemLp f 2 (volume.restrict S))
    (F : Domain n × ℝ → E)
    (H : C(Icc a 1, Lp E 2 (volume.restrict S)))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 (volume.restrict S),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t)))
    (hcontain : ∀ t : Icc ρ 1, ∀ x ∈ U, t.val⁻¹ • x ∈ S)
    (hFormula : ∀ t ∈ Ioo ρ 1, ∀ x ∈ U, F (x, t) = f (t⁻¹ • x)) :
    (H ⟨1, haρ.trans hρ1.le, le_rfl⟩ : Domain n → E) =ᵐ[volume.restrict U] f := by
  let μ := (volume : Measure (Domain n)).restrict U
  let ν := (volume : Measure (Domain n)).restrict S
  have hμν : μ ≤ ν := Measure.restrict_mono_set volume hUS
  let L : Lp E 2 ν →L[ℝ] Lp E 2 μ := Lp.LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by norm_num) (by simpa only [one_smul] using hμν)
  let τ : C(Icc ρ 1, Icc a 1) :=
    ⟨fun t => ⟨t.val, haρ.trans t.property.1, t.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let K : C(Icc ρ 1, Lp E 2 μ) := ⟨fun t => L (H (τ t)),
    L.continuous.comp (H.continuous.comp τ.continuous)⟩
  obtain ⟨J, _hJ, ⟨hfU, hEndJ⟩, hUnique⟩ :=
    exists_inverse_dilation_L2_trace_on_subset hS hU hf hρ hρ1 hcontain
  have hK : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo ρ 1,
      ∃ hs : MemLp (fun x : Domain n => f (t⁻¹ • x)) 2 μ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (t⁻¹ • x)) := by
    filter_upwards [hH] with t ht htI
    obtain ⟨hFt, hClass⟩ := ht ⟨haρ.trans_lt htI.1, htI.2⟩
    have hSmall := hFt.mono_measure hμν
    have hRaw : (fun x => F (x, t)) =ᵐ[μ] (fun x => f (t⁻¹ • x)) := by
      filter_upwards [ae_restrict_mem hU] with x hx
      exact hFormula t htI x hx
    have hft := hSmall.ae_eq hRaw
    refine ⟨hft, ?_⟩
    change L (H ⟨t, (haρ.trans_lt htI.1).le, htI.2.le⟩) = _
    rw [hClass]
    exact (lp_two_measure_restriction_toLp hμν _ hFt hSmall).trans
      (MemLp.toLp_congr hSmall hft hRaw)
  have hKJ : K = J := hUnique K hK
  have hEndpoint : L (H ⟨1, haρ.trans hρ1.le, le_rfl⟩) = hfU.toLp f := by
    change K ⟨1, hρ1.le, le_rfl⟩ = _
    rw [hKJ]
    exact hEndJ
  have hCoe := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
    (by norm_num) (show μ ≤ (1 : ℝ≥0∞) • ν by simpa only [one_smul] using hμν)
      (H ⟨1, haρ.trans hρ1.le, le_rfl⟩)
  change (L _) =ᵐ[μ] _ at hCoe
  rw [hEndpoint] at hCoe
  exact hCoe.symm.trans hfU.coeFn_toLp

end StratificationTheory
