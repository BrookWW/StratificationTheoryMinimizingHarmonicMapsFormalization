-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.Sobolev
public import HarmonicMaps.Energy
public import StratificationTheory.Foundation.AngularL2Membership
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra
import StratificationTheory.Providers.RadialTraceGluing

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Matching genuine native-L2 radial traces glue the original inner map and
outer annular map, with their displayed piecewise weak columns and exact
additive energy. No pointwise equality of raw boundary values is assumed. -/
theorem memW12_radial_trace_gluing {n q : ℕ} (hn : 2 ≤ n)
    (c : Domain n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u w : Domain n → Ambient q) (Du Dw : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain c r) u Du)
    (hw : MemW12 ⟨{x | r < ‖x - c‖ ∧ ‖x - c‖ < R},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ w Dw) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let a := r / 2
    let b := (r + R) / 2
    ∀ (H : C(Icc a r, Lp (Ambient q) 2 σ)) (K : C(Icc r b, Lp (Ambient q) 2 σ)),
      (∀ᵐ (s : ℝ) ∂volume, ∀ hs : s ∈ Ioo a r,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + s • θ.val)) 2 σ,
          H ⟨s, hs.1.le, hs.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + s • θ.val))) →
      (∀ᵐ (s : ℝ) ∂volume, ∀ hs : s ∈ Ioo r b,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + s • θ.val)) 2 σ,
          K ⟨s, hs.1.le, hs.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + s • θ.val))) →
      H ⟨r, by dsimp only [a]; linarith only [hr], le_rfl⟩ =
      K ⟨r, le_rfl, by dsimp only [b]; linarith only [hrR]⟩ →
      let f : Domain n → Ambient q := fun x => if ‖x - c‖ < r then u x else w x
      let Df : Domain n → Gradient n q := fun x i =>
        if ‖x - c‖ < r then Du x i else Dw x i
      MemW12 (ballDomain c R) f Df ∧
      (∫ x in ball c R, hsNormSq (Df x)) =
        (∫ x in ball c r, hsNormSq (Du x)) +
          (∫ x in {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R}, hsNormSq (Dw x)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.RadialTraceGluing.result hn c hr hrR u w Du Dw hu hw
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
