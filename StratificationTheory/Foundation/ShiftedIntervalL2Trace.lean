module

public import StratificationTheory.Foundation.PositiveIntervalL2Trace

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- A complete original unit trace transports to an arbitrarily translated
positive physical segment, with both original endpoint classes. -/
theorem exists_shifted_segment_L2_trace_of_unit_interval {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (F : X × ℝ → E) (H : C(Icc (-1 : ℝ) 1, Lp E 2 μ))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t))) :
    ∃ K : C(Icc a (a + ε), Lp E 2 μ),
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a (a + ε),
        ∃ hs : MemLp (fun x => F (x, (r - a) / (ε / 2) - 1)) 2 μ,
          K ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => F (x, (r - a) / (ε / 2) - 1))) ∧
      K ⟨a, le_rfl, by linarith⟩ = H ⟨-1, le_rfl, by norm_num⟩ ∧
      K ⟨a + ε, by linarith, le_rfl⟩ = H ⟨1, by norm_num, le_rfl⟩ := by
  obtain ⟨J, _hCommute, hJ, hJ₀, hJ₁, _hUnique⟩ :=
    exists_positive_segment_L2_trace_of_unit_interval hε F H hH
  have hτ (r : Icc a (a + ε)) : r.val - a ∈ Icc (0 : ℝ) ε :=
    ⟨by linarith [r.property.1], by linarith [r.property.2]⟩
  let τ : C(Icc a (a + ε), Icc (0 : ℝ) ε) :=
    ⟨fun r => ⟨r.val - a, hτ r⟩, (continuous_subtype_val.sub continuous_const).subtype_mk hτ⟩
  let K := J.comp τ
  refine ⟨K, ?_, ?_, ?_⟩
  · have hPull := (measurePreserving_add_right (volume : Measure ℝ) (-a)).quasiMeasurePreserving.ae hJ
    filter_upwards [hPull] with r hr hrI
    have hr' : r - a ∈ Ioo (0 : ℝ) ε := ⟨by linarith [hrI.1], by linarith [hrI.2]⟩
    change ∃ hs : MemLp (fun x => F (x, (r - a) / (ε / 2) - 1)) 2 μ,
      J ⟨r - a, hr'.1.le, hr'.2.le⟩ = hs.toLp (fun x => F (x, (r - a) / (ε / 2) - 1))
    simpa only [sub_eq_add_neg] using hr (by simpa only [sub_eq_add_neg] using hr')
  · change J ⟨a - a, hτ ⟨a, le_rfl, by linarith⟩⟩ = _
    simpa only [sub_self] using hJ₀
  · change J ⟨a + ε - a, hτ ⟨a + ε, by linarith, le_rfl⟩⟩ = _
    simpa only [add_sub_cancel_left] using hJ₁

end StratificationTheory
