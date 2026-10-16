module

public import StratificationTheory.Foundation.RadialTraceCompatibility

/-!
# One original trace across translated coordinate cuts

Translated raw parameterizations determine the same continuous L2 curve on
their complete closed common carrier. In particular, original raw classes at
two selected cuts belong to one curve on the intervening physical segment.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- A literal translation of raw time coordinates identifies the entire
continuous native L2 trace, including every cut in the closed carrier. -/
theorem continuous_L2_traces_agree_after_time_translation
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {a b c d s : ℝ} (hab : a < b)
    {f g : α × ℝ → E}
    (H : C(Icc a b, Lp E 2 μ)) (K : C(Icc c d, Lp E 2 μ))
    (hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, r)) 2 μ,
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r)))
    (hK : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo c d,
      ∃ hslice : MemLp (fun x => g (x, r)) 2 μ,
        K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => g (x, r)))
    (hclosed : ∀ r ∈ Icc a b, r - s ∈ Icc c d)
    (hopen : ∀ r ∈ Ioo a b, r - s ∈ Ioo c d)
    (hraw : ∀ (x : α) (r : ℝ), g (x, r - s) = f (x, r)) :
    ∀ r : Icc a b, H r = K ⟨r.val - s, hclosed r.val r.property⟩ := by
  let τ : C(Icc a b, Icc c d) :=
    ⟨fun r => ⟨r.val - s, hclosed r.val r.property⟩,
      (continuous_subtype_val.sub continuous_const).subtype_mk _⟩
  let L : C(Icc a b, Lp E 2 μ) := K.comp τ
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae hK
  have hL : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => g (x, r - s)) 2 μ,
        L ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => g (x, r - s)) := by
    filter_upwards [hshift] with r hr hrI
    have hr' : ∀ h : r - s ∈ Ioo c d,
        ∃ hslice : MemLp (fun x => g (x, r - s)) 2 μ,
          K ⟨r - s, h.1.le, h.2.le⟩ = hslice.toLp (fun x => g (x, r - s)) := by
      simpa only [sub_eq_add_neg] using hr
    exact hr' (hopen r hrI)
  have hHL : H = L := continuous_Lp_representatives_eq_of_ae_slices
    (f := f) (g := fun p : α × ℝ => g (p.1, p.2 - s)) hab H L hH hL
    (Eventually.of_forall fun r _hr => Eventually.of_forall fun x => (hraw x r).symm)
  exact fun r => congrArg (fun J : C(Icc a b, Lp E 2 μ) => J r) hHL

/-- Original raw classes at two translated cuts are the two endpoints of
one continuous native L2 curve on their actual intervening time segment.
The agreement of the two full trace curves is derived from their original
raw slices, rather than assumed. -/
theorem exists_one_L2_trace_between_translated_raw_cuts
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {a b c d ε : ℝ} (hε : 0 < ε)
    (ha : a < 0) (hb : ε < b) (hc : c < 0) (hd : 0 < d)
    {f g : α × ℝ → E}
    (H : C(Icc a b, Lp E 2 μ)) (K : C(Icc c d, Lp E 2 μ))
    (hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, r)) 2 μ,
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r)))
    (hK : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo c d,
      ∃ hslice : MemLp (fun x => g (x, r)) 2 μ,
        K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => g (x, r)))
    (hclosed : ∀ r ∈ Icc a b, r - ε ∈ Icc c d)
    (hopen : ∀ r ∈ Ioo a b, r - ε ∈ Ioo c d)
    (hraw : ∀ (x : α) (r : ℝ), g (x, r - ε) = f (x, r))
    (hf₀ : MemLp (fun x => f (x, 0)) 2 μ)
    (hH₀ : H ⟨0, ha.le, (hε.trans hb).le⟩ = hf₀.toLp (fun x => f (x, 0)))
    (hg₀ : MemLp (fun x => g (x, 0)) 2 μ)
    (hK₀ : K ⟨0, hc.le, hd.le⟩ = hg₀.toLp (fun x => g (x, 0))) :
    ∃ J : C(Icc (0 : ℝ) ε, Lp E 2 μ),
      (∀ r : Icc (0 : ℝ) ε, J r = H ⟨r.val, ha.le.trans r.property.1, r.property.2.trans hb.le⟩) ∧
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
        ∃ hslice : MemLp (fun x => f (x, r)) 2 μ,
          J ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r))) ∧
      J ⟨0, le_rfl, hε.le⟩ = hf₀.toLp (fun x => f (x, 0)) ∧
      J ⟨ε, hε.le, le_rfl⟩ = hg₀.toLp (fun x => g (x, 0)) ∧
      ∀ L : C(Icc (0 : ℝ) ε, Lp E 2 μ),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
          ∃ hslice : MemLp (fun x => f (x, r)) 2 μ,
            L ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r))) → L = J := by
  let τ : C(Icc (0 : ℝ) ε, Icc a b) :=
    ⟨fun r => ⟨r.val, ha.le.trans r.property.1, r.property.2.trans hb.le⟩,
      continuous_subtype_val.subtype_mk _⟩
  let J : C(Icc (0 : ℝ) ε, Lp E 2 μ) := H.comp τ
  have hJ : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
      ∃ hslice : MemLp (fun x => f (x, r)) 2 μ,
        J ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r)) := by
    filter_upwards [hH] with r hr hrI
    exact hr ⟨ha.trans hrI.1, hrI.2.trans hb⟩
  have hab : a < b := ha.trans (hε.trans hb)
  have hagree := continuous_L2_traces_agree_after_time_translation hab H K hH hK hclosed hopen hraw
  have hupper : J ⟨ε, hε.le, le_rfl⟩ = hg₀.toLp (fun x => g (x, 0)) := by
    have h := hagree ⟨ε, ha.le.trans hε.le, hb.le⟩
    change H ⟨ε, ha.le.trans hε.le, hb.le⟩ = _
    simpa only [sub_self, hK₀] using h
  refine ⟨J, fun _ => rfl, hJ, hH₀, hupper, ?_⟩
  intro L hL
  exact continuous_Lp_representatives_eq_of_ae_slices hε L J hL hJ
    (Eventually.of_forall fun _ _ => Filter.EventuallyEq.rfl)

end StratificationTheory
