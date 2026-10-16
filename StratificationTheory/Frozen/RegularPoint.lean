module

public import HarmonicMaps.Sobolev

@[expose] public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StratificationTheory

def IsRegularPoint {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (a : Ω.val) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball a.val r ⊆ Ω.val ∧
    ∃ w : Domain n → Ambient q,
      ContDiffOn ℝ ∞ w (Metric.ball a.val r) ∧
      w =ᵐ[volume.restrict (Metric.ball a.val r)] u

end StratificationTheory
