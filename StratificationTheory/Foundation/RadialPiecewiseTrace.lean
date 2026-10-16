module

public import StratificationTheory.Foundation.ContinuousLpTraceGluing
public import StratificationTheory.Foundation.RadialTraceCompatibility

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Matching radial L2 curves concatenate into the full continuous radial
trace of the literal original piecewise map. -/
theorem exists_radial_trace_piecewise {n q : ℕ}
    (c : Domain n) (σ : Measure (sphere (0 : Domain n) 1))
    {a r b : ℝ} (ha : 0 < a) (har : a < r) (hrb : r < b)
    (u w : Domain n → Ambient q)
    (H : C(Icc a r, Lp (Ambient q) 2 σ))
    (K : C(Icc r b, Lp (Ambient q) 2 σ))
    (hH : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo a r,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + s • θ.val)) 2 σ,
        H ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + s • θ.val)))
    (hK : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo r b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + s • θ.val)) 2 σ,
        K ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + s • θ.val)))
    (hmatch : H ⟨r, har.le, le_rfl⟩ = K ⟨r, le_rfl, hrb.le⟩) :
    let f : Domain n → Ambient q := fun x => if ‖x - c‖ < r then u x else w x
    ∃ J : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ s : Icc a r, J ⟨s.val, s.property.1, s.property.2.trans hrb.le⟩ = H s) ∧
      (∀ s : Icc r b, J ⟨s.val, har.le.trans s.property.1, s.property.2⟩ = K s) ∧
      (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => f (c + s • θ.val)) 2 σ,
          J ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => f (c + s • θ.val))) := by
  intro f
  obtain ⟨J, hleft, hright, hJ⟩ := exists_continuous_lp_trace_piecewise σ har hrb
    (fun p : sphere (0 : Domain n) 1 × ℝ => u (c + p.2 • p.1.val))
    (fun p : sphere (0 : Domain n) 1 × ℝ => w (c + p.2 • p.1.val)) H K hH hK hmatch
  refine ⟨J, hleft, hright, ?_⟩
  filter_upwards [hJ] with s hsJ hs
  obtain ⟨hL, hEq⟩ := hsJ hs
  have hspos : 0 < s := ha.trans hs.1
  have heq : (fun θ : sphere (0 : Domain n) 1 =>
      if s < r then u (c + s • θ.val) else w (c + s • θ.val)) =
        (fun θ : sphere (0 : Domain n) 1 => f (c + s • θ.val)) := by
    funext θ
    have hθ : ‖θ.val‖ = (1 : ℝ) := (mem_sphere_zero_iff_norm).mp θ.property
    have hrad : ‖c + s • θ.val - c‖ = s := by
      simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hspos.le, hθ, mul_one]
    simp only [f, hrad]
  let hLF := hL.ae_eq (Eventually.of_forall fun θ => congrFun heq θ)
  refine ⟨hLF, hEq.trans ?_⟩
  exact hL.toLp_congr hLF (Eventually.of_forall fun θ => congrFun heq θ)

end StratificationTheory
