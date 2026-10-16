module

public import StratificationTheory.Frozen.AmbientRadialTraceWellDefined
public import HarmonicMaps.Analysis.AffineBallMeasure

public section

open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory.Compactness

/-- A positive spatial dilation pulls back the original continuous radial
trace, including its complete raw interior-slice normalization. -/
theorem exists_dilated_inner_radial_trace {n q : ℕ}
    (σ : Measure (sphere (0 : Domain n) 1))
    (u : Domain n → Ambient q) (c : Domain n)
    {a b s t lo : ℝ} (hs : 0 < s) (ht : 0 < t) (hlo : 0 < lo)
    (hscale : t * lo = s)
    (has : a ≤ s / 2) (hsb : s ≤ b)
    (H : C(Icc a b, Lp (Ambient q) 2 σ))
    (hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2 σ,
        H ⟨r, hr.1.le, hr.2.le⟩ =
          hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val))) :
    let w : Domain n → Ambient q := fun x => u (c + t • (x - c))
    ∃ J : C(Icc (lo / 2) lo, Lp (Ambient q) 2 σ),
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (lo / 2) lo,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + r • θ.val)) 2 σ,
          J ⟨r, hr.1.le, hr.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + r • θ.val))) ∧
      J ⟨lo, by linarith only [hlo], le_rfl⟩ =
        H ⟨s, has.trans (by linarith only [hs]), hsb⟩ := by
  intro w
  have hτ (r : Icc (lo / 2) lo) : t * r.val ∈ Icc a b := by
    have hlow := mul_le_mul_of_nonneg_left r.property.1 ht.le
    have hupp := mul_le_mul_of_nonneg_left r.property.2 ht.le
    constructor
    · calc
        a ≤ s / 2 := has
        _ = t * (lo / 2) := by rw [← mul_div_assoc, hscale]
        _ ≤ t * r.val := hlow
    · exact (hupp.trans_eq hscale).trans hsb
  let τ : C(Icc (lo / 2) lo, Icc a b) :=
    ⟨fun r => ⟨t * r.val, hτ r⟩,
      (continuous_const.mul continuous_subtype_val).subtype_mk hτ⟩
  let J := H.comp τ
  refine ⟨J, ?_, ?_⟩
  · have hHpull : ∀ᵐ r : ℝ ∂volume, ∀ hr : t * r ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + (t * r) • θ.val)) 2 σ,
          H ⟨t * r, hr.1.le, hr.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + (t * r) • θ.val)) := by
      simpa only [smul_eq_mul] using
        ((volume : Measure ℝ).quasiMeasurePreserving_smul ht.ne').ae hH
    filter_upwards [hHpull] with r hHr hr
    have htr : t * r ∈ Ioo a b := by
      have hlow := mul_lt_mul_of_pos_left hr.1 ht
      have hupp := mul_lt_mul_of_pos_left hr.2 ht
      constructor
      · calc
          a ≤ s / 2 := has
          _ = t * (lo / 2) := by rw [← mul_div_assoc, hscale]
          _ < t * r := hlow
      · exact (hupp.trans_eq hscale).trans_le hsb
    obtain ⟨hslice, hclass⟩ := hHr htr
    have hfun : (fun θ : sphere (0 : Domain n) 1 => w (c + r • θ.val)) =
        (fun θ : sphere (0 : Domain n) 1 => u (c + (t * r) • θ.val)) := by
      funext θ
      simp only [w, add_sub_cancel_left, smul_smul]
    have hslice' : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + r • θ.val)) 2 σ := by
      rw [hfun]
      exact hslice
    refine ⟨hslice', ?_⟩
    change H ⟨t * r, htr.1.le, htr.2.le⟩ = _
    rw [hclass]
    exact MemLp.toLp_congr hslice hslice'
      (Eventually.of_forall fun θ => (congrFun hfun θ).symm)
  · apply congrArg H
    exact Subtype.ext hscale

end StratificationTheory.Compactness
