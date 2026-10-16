module

public import StratificationTheory.Foundation.CoordinateTraceRestrictions

/-!
# The continuous L2 trace of an affine edge interpolation

The same affine map has a continuous time curve in the original spatial L2
space. Every time slice, including both boundary times, represents that curve;
interior a.e. slice classes uniquely determine it.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Actual affine slices of two original L2 classes have a single continuous
Lp trace curve with the original boundary classes. Uniqueness uses only the
interior a.e. slices of a competing continuous curve. -/
theorem affine_pair_continuous_lp_trace {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) {c d : ℝ} (hcd : c < d)
    {F G f h : X → Ambient q} (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (hFae : F =ᵐ[μ] f) (hGae : G =ᵐ[μ] h) :
    let W : X → ℝ → Ambient q := fun x t =>
      (1 - (t - c) / (d - c)) • F x + ((t - c) / (d - c)) • G x
    ∃ H : C(Icc c d, Lp (Ambient q) 2 μ),
      (∀ t : Icc c d, H t = (1 - ((t : ℝ) - c) / (d - c)) • hf.toLp f +
        (((t : ℝ) - c) / (d - c)) • hh.toLp h) ∧
      (∀ t : Icc c d, ∃ ht : MemLp (fun x => W x t) 2 μ,
        H t = ht.toLp (fun x => W x t)) ∧
      H ⟨c, le_rfl, hcd.le⟩ = hf.toLp f ∧
      H ⟨d, hcd.le, le_rfl⟩ = hh.toLp h ∧
      ∀ K : C(Icc c d, Lp (Ambient q) 2 μ),
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c d,
          ∃ hslice : MemLp (fun x => W x t) 2 μ,
            K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => W x t)) → K = H := by
  intro W
  have hF : MemLp F 2 μ := hf.ae_eq hFae.symm
  have hG : MemLp G 2 μ := hh.ae_eq hGae.symm
  let α : Icc c d → ℝ := fun t => ((t : ℝ) - c) / (d - c)
  have hα : Continuous α :=
    (continuous_subtype_val.sub continuous_const).div_const (d - c)
  let H : C(Icc c d, Lp (Ambient q) 2 μ) :=
    ⟨fun t => (1 - α t) • hf.toLp f + α t • hh.toLp h,
      ((continuous_const.sub hα).smul continuous_const).add (hα.smul continuous_const)⟩
  have hraw (t : Icc c d) : ∃ ht : MemLp (fun x => W x t) 2 μ,
      H t = ht.toLp (fun x => W x t) := by
    have ht := (hF.const_smul (1 - α t)).add (hG.const_smul (α t))
    refine ⟨ht, ?_⟩
    change (1 - α t) • hf.toLp f + α t • hh.toLp h = ht.toLp _
    rw [(hF.const_smul (1 - α t)).toLp_add (hG.const_smul (α t)),
      MemLp.toLp_const_smul (1 - α t) hF, MemLp.toLp_const_smul (α t) hG,
      hF.toLp_congr hf hFae, hG.toLp_congr hh hGae]
  refine ⟨H, fun _ => rfl, hraw, ?_, ?_, ?_⟩
  · change (1 - (c - c) / (d - c)) • hf.toLp f + ((c - c) / (d - c)) • hh.toLp h = _
    simp only [sub_self, zero_div, sub_zero, one_smul, zero_smul, add_zero]
  · change (1 - (d - c) / (d - c)) • hf.toLp f + ((d - c) / (d - c)) • hh.toLp h = _
    simp only [div_self (sub_ne_zero.mpr hcd.ne'), sub_self, zero_smul, one_smul, zero_add]
  · intro K hK
    have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c d,
        (K - H) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 μ)) := by
      filter_upwards [hK] with t ht htI
      obtain ⟨hKt, hKEq⟩ := ht htI
      obtain ⟨hHt, hHEq⟩ := hraw ⟨t, htI.1.le, htI.2.le⟩
      change K ⟨t, htI.1.le, htI.2.le⟩ - H ⟨t, htI.1.le, htI.2.le⟩ ∈ ({0} : Set _)
      rw [mem_singleton_iff, sub_eq_zero]
      exact hKEq.trans ((hKt.toLp_congr hHt (Filter.EventuallyEq.rfl)).trans hHEq.symm)
    have hzero := continuous_interval_mem_closed_of_ae hcd (K - H) isClosed_singleton hdiff
    apply ContinuousMap.ext
    intro t
    exact sub_eq_zero.mp (mem_singleton_iff.mp (hzero t))

end StratificationTheory
