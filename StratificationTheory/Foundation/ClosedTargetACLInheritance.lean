module

public import StratificationTheory.Foundation.IntervalClosedConstraints
public import StratificationTheory.Foundation.CoordinateACLRepresentative

/-!
# Closed target inheritance on absolutely continuous lines

An absolutely continuous representative of an almost-everywhere target-valued
map lies in the same closed target at every point of the closed interval.
-/

public section
open MeasureTheory Set Filter
open scoped Topology
namespace StratificationTheory

/-- Closed target membership of an a.e.-equal raw interval map extends to
every value of its absolutely continuous representative, including endpoints. -/
theorem absolutelyContinuous_interval_mem_closed_of_ae {E : Type*}
    [NormedAddCommGroup E] {a b : ℝ} (hab : a < b)
    {F f : ℝ → E} (hF : AbsolutelyContinuousOnInterval F a b)
    (hFf : F =ᵐ[volume.restrict (Ioo a b)] f)
    {N : Set E} (hN : IsClosed N)
    (hfN : ∀ᵐ t ∂volume.restrict (Ioo a b), f t ∈ N) :
    ∀ t ∈ Icc a b, F t ∈ N := by
  have hc : ContinuousOn F (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hF.continuousOn
  let H : C(Icc a b, E) := ⟨fun t => F t.val, hc.restrict⟩
  have hFN : ∀ᵐ t ∂volume.restrict (Ioo a b), F t ∈ N := by
    filter_upwards [hFf, hfN] with t ht hNf
    exact ht.symm ▸ hNf
  have hHN : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      H ⟨t, ht.1.le, ht.2.le⟩ ∈ N := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hFN] with t ht hI
    exact ht hI
  intro t ht
  exact continuous_interval_mem_closed_of_ae hab H hN hHN ⟨t, ht⟩

/-- A jointly a.e.-equal product representative inherits a closed target on
every point of almost every absolutely continuous interval fiber. -/
theorem ae_fiber_interval_mem_closed_of_ae {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [SigmaFinite μ] {a b : ℝ} (hab : a < b)
    {F f : α × ℝ → E}
    (hFf : F =ᵐ[μ.prod (volume.restrict (Ioo a b))] f)
    (hFac : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun t => F (x, t)) a b)
    {N : Set E} (hN : IsClosed N)
    (hfN : ∀ᵐ p ∂μ.prod (volume.restrict (Ioo a b)), f p ∈ N) :
    ∀ᵐ x ∂μ, ∀ t ∈ Icc a b, F (x, t) ∈ N := by
  have hEq := Measure.ae_ae_of_ae_prod hFf
  have hTarget := Measure.ae_ae_of_ae_prod hfN
  filter_upwards [hEq, hFac, hTarget] with x hx hxac hxN
  exact absolutelyContinuous_interval_mem_closed_of_ae hab hxac hx hN hxN

end StratificationTheory
