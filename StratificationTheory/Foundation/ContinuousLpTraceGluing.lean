module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section
open MeasureTheory Set Filter
namespace StratificationTheory

/-- Matching continuous L2 slice representatives concatenate on the entire
closed interval and represent the literal time-piecewise raw map. -/
theorem exists_continuous_lp_trace_piecewise
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    {a r b : ℝ} (har : a < r) (hrb : r < b) (f g : α × ℝ → E)
    (H : C(Icc a r, Lp E 2 μ)) (K : C(Icc r b, Lp E 2 μ))
    (hH : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo a r,
      ∃ hslice : MemLp (fun θ : α => f (θ, s)) 2 μ,
        H ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ => f (θ, s)))
    (hK : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo r b,
      ∃ hslice : MemLp (fun θ : α => g (θ, s)) 2 μ,
        K ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ => g (θ, s)))
    (hmatch : H ⟨r, har.le, le_rfl⟩ = K ⟨r, le_rfl, hrb.le⟩) :
    ∃ J : C(Icc a b, Lp E 2 μ),
      (∀ s : Icc a r, J ⟨s.val, s.property.1, s.property.2.trans hrb.le⟩ = H s) ∧
      (∀ s : Icc r b, J ⟨s.val, har.le.trans s.property.1, s.property.2⟩ = K s) ∧
      (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ : α => if s < r then f (θ, s) else g (θ, s)) 2 μ,
          J ⟨s, hs.1.le, hs.2.le⟩ =
            hslice.toLp (fun θ => if s < r then f (θ, s) else g (θ, s))) := by
  letI : Fact (a ≤ r) := ⟨har.le⟩
  letI : Fact (r ≤ b) := ⟨hrb.le⟩
  have hmatch' : H ⊤ = K ⊥ := hmatch
  let J := ContinuousMap.concatCM ⟨(H, K), hmatch'⟩
  have hleft (s : Icc a r) :
      J ⟨s.val, s.property.1, s.property.2.trans hrb.le⟩ = H s :=
    ContinuousMap.concatCM_left (a := a) (b := r) (c := b)
      (fg := ⟨(H, K), hmatch'⟩) s.property.2
  have hright (s : Icc r b) :
      J ⟨s.val, har.le.trans s.property.1, s.property.2⟩ = K s :=
    ContinuousMap.concatCM_right (a := a) (b := r) (c := b)
      (fg := ⟨(H, K), hmatch'⟩) s.property.1
  refine ⟨J, hleft, hright, ?_⟩
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    exact ae_iff.mpr (by simpa only [not_not, Set.setOf_eq_eq_singleton] using
      (measure_singleton r : (volume : Measure ℝ) {r} = 0))
  filter_upwards [hH, hK, hne] with s hHs hKs hsr hs
  by_cases hsr' : s < r
  · obtain ⟨hL, hEq⟩ := hHs ⟨hs.1, hsr'⟩
    refine ⟨by simpa only [if_pos hsr'] using hL, ?_⟩
    simpa only [if_pos hsr'] using (hleft ⟨s, hs.1.le, hsr'.le⟩).trans hEq
  · have hrs : r < s := lt_of_le_of_ne (le_of_not_gt hsr') (Ne.symm hsr)
    obtain ⟨hL, hEq⟩ := hKs ⟨hrs, hs.2⟩
    refine ⟨by simpa only [if_neg hsr'] using hL, ?_⟩
    simpa only [if_neg hsr'] using (hright ⟨s, hrs.le, hs.2.le⟩).trans hEq

end StratificationTheory
