module

public import StratificationTheory.Foundation.BoundedFiberL2Trace

/-!
# Original raw traces from bounded continuous line data

The original interior raw slice classes and a chosen original raw cut class
are retained by one continuous native L2 curve. The proof uses the bounded
line representative and raw a.e. recovery, without assuming L2 convergence
to the cut or equality of the cut with a canonical trace.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original raw slice measurability, bounded continuous line data and raw
recovery produce the actual continuous L2 trace and its original chosen cut
class. A desired trace or L2 cut limit is not an input. -/
theorem exists_raw_L2_trace_of_bounded_line_data
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) {f F : α × ℝ → E} {M : ℝ}
    (hmeas : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      AEStronglyMeasurable (fun x => f (x, t)) μ)
    (hFae : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      (fun x => F (x, t)) =ᵐ[μ] (fun x => f (x, t)))
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun t => F (x, t)) (Icc a b))
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ Icc a b, ‖F (x, t)‖ ≤ M)
    (c : Icc a b) (hcut : (fun x => F (x, c.val)) =ᵐ[μ] (fun x => f (x, c.val))) :
    ∃ H : C(Icc a b, Lp E 2 μ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) ∧
      (∃ hslice : MemLp (fun x => f (x, c.val)) 2 μ,
        H c = hslice.toLp (fun x => f (x, c.val))) ∧
      ∀ K : C(Icc a b, Lp E 2 μ),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
            K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) → K = H := by
  have hFmeas : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      AEStronglyMeasurable (fun x => F (x, t)) μ := by
    filter_upwards [hmeas, hFae] with t hmt hFt ht
    exact (hmt ht).congr (hFt ht).symm
  obtain ⟨H, hH, _hHunique⟩ :=
    exists_continuous_L2_trace_of_bounded_fiber_continuity μ hab hFmeas hcont hbound
  have hraw : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t)) := by
    filter_upwards [hFae] with t hFt ht
    obtain ⟨hFtL, hHt⟩ := hH ⟨t, ht.1.le, ht.2.le⟩
    have hftL := hFtL.ae_eq (hFt ht)
    exact ⟨hftL, hHt.trans (hFtL.toLp_congr hftL (hFt ht))⟩
  refine ⟨H, hraw, ?_, ?_⟩
  · obtain ⟨hFc, hHc⟩ := hH c
    have hfc := hFc.ae_eq hcut
    exact ⟨hfc, hHc.trans (hFc.toLp_congr hfc hcut)⟩
  · intro K hK
    exact continuous_Lp_representatives_eq_of_ae_slices hab K H hK hraw
      (Eventually.of_forall fun _ _ => Filter.EventuallyEq.rfl)

end StratificationTheory
