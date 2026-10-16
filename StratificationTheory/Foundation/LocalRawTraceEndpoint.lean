module

public import StratificationTheory.Foundation.ContinuousTraceEndpoint

/-!
# Local original raw limits identify native endpoint classes

The canonical curve and genuine local L2 errors supply the endpoint's L2
qualification internally. Restricting an actual larger-patch limit keeps
the same raw map and endpoint class.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- A genuine larger-patch raw limit determines the original left endpoint
on a subpatch, including its L2 qualification. -/
theorem exists_left_trace_class_of_local_raw_L2_limit {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (μ ν : Measure X) (hμν : μ ≤ ν)
    {δ : ℝ} (hδ : 0 < δ) (J : C(Icc (0 : ℝ) δ,Lp E 2 μ))
    (f : X × ℝ → E) (g : X → E)
    (hJ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) δ,
      ∃ hs : MemLp (fun x => f (x,t)) 2 μ,
        J ⟨t,ht.1.le,ht.2.le⟩ = hs.toLp (fun x => f (x,t)))
    (hErr : ∀ᶠ t in 𝓝[>] (0 : ℝ), MemLp (fun x => f (x,t) - g x) 2 ν)
    (hLim : Tendsto (fun t => eLpNorm (fun x => f (x,t) - g x) 2 ν)
      (𝓝[>] 0) (𝓝 0)) :
    ∃ hg : MemLp g 2 μ, J ⟨0,le_rfl,hδ.le⟩ = hg.toLp g := by
  obtain ⟨β,hβ,hβErr⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hErr
  have hmin : 0 < min δ β := lt_min hδ hβ
  have hNonzero : (volume : Measure ℝ) (Ioo (0 : ℝ) (min δ β)) ≠ 0 := by
    rw [Real.volume_Ioo,sub_zero]
    exact (ENNReal.ofReal_pos.mpr hmin).ne'
  have hAE : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (min δ β)), MemLp g 2 μ := by
    filter_upwards [ae_restrict_of_ae hJ,ae_restrict_mem measurableSet_Ioo] with t ht htI
    obtain ⟨hs,_hClass⟩ := ht ⟨htI.1,htI.2.trans_le (min_le_left _ _)⟩
    have he := (hβErr ⟨htI.1,htI.2.trans_le (min_le_right _ _)⟩).mono_measure hμν
    have hh := hs.sub he
    change MemLp (fun x => f (x,t) - (f (x,t) - g x)) 2 μ at hh
    simpa only [sub_sub_cancel] using hh
  obtain ⟨t,_htI,hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hNonzero hAE
  have hLimit : Tendsto (fun t => eLpNorm (fun x => f (x,t) - g x) 2 μ)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ hμν)
  exact ⟨hg,continuous_L2_trace_left_endpoint_of_raw_limit μ hδ J hJ hg hLimit⟩

end StratificationTheory
