/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Foundation.DensityBounds
public import HolderToCK.Analysis.Bootstrap.AffineMinimizer

import StratificationTheory.Foundation.NormalizedEnergyOrder
import StratificationTheory.Foundation.PositiveRadiusLimits

/-!
# Density of an actual affine pullback on a contained ball

The imported affine minimizing-data theorem supplies Sobolev membership,
target membership and minimality of the displayed rescaled map and gradient.
The registered density of that map equals the original density at the
corresponding center, at every point of the rescaled ball.
-/

public section

open HarmonicMaps Filter Set
open scoped Topology

namespace StratificationTheory

theorem affineBall_pullback_point_mem {n : ℕ} (Ω : OpenDomain n)
    (a : Domain n) (R ρ : PositiveRadius)
    (hball : Metric.closedBall a R.val ⊆ Ω.val)
    (b : (ballDomain (0 : Domain n) (R.val / ρ.val)).val) :
    a + ρ.val • b.val ∈ Ω.val := by
  have hb : a + ρ.val • b.val ∈ Metric.ball a R.val := by
    simpa only [sub_zero] using
      (affineBall_mem_ball_iff a (0 : Domain n) ρ.property R.val b.val).mpr b.property
  exact hball (Metric.ball_subset_closedBall hb)

/-- Positive affine scaling preserves the actual registered density. All
rescaled minimizing data are supplied by the imported transport theorem. -/
theorem density_affineBall_pullback {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Domain n) (R ρ : PositiveRadius)
    (hball : Metric.closedBall a R.val ⊆ Ω.val) :
    let data := HolderToCK.affineBall_minimizer_transport_on N Ω a R ρ u Du
      hball hu hN hmin
    ∀ b : (ballDomain (0 : Domain n) (R.val / ρ.val)).val,
      density hn data.2.2 data.1 data.2.1 b =
        density hn hmin hu hN ⟨a + ρ.val • b.val,
          affineBall_pullback_point_mem Ω a R ρ hball b⟩ := by
  intro data b
  let c : Ω.val := ⟨a + ρ.val • b.val,
    affineBall_pullback_point_mem Ω a R ρ hball b⟩
  have hscaled : Tendsto (fun r : PositiveRadius =>
      (normalizedEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i) b.val r).toReal)
      atBot (𝓝 (density hn hmin hu hN c)) := by
    have hmul : Tendsto (fun r : PositiveRadius =>
        (⟨ρ.val * r.val, mul_pos ρ.property r.property⟩ : PositiveRadius)) atBot atBot :=
      positiveRadius_mul_tendsto_atBot ρ.property
    have hcomp := (normalizedEnergy_tendsto_density_atBot hn hmin hu hN c).comp hmul
    have heq : (fun r : PositiveRadius =>
        (normalizedEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i) b.val r).toReal) =
        (fun r : PositiveRadius =>
          (normalizedEnergy Du c.val ⟨ρ.val * r.val, mul_pos ρ.property r.property⟩).toReal) := by
      funext r
      exact congrArg ENNReal.toReal (normalizedEnergy_affine_pullback a b.val ρ r Du)
    rw [heq]
    exact hcomp
  have hfilter : (atBot : Filter PositiveRadius) =
      comap (Subtype.val : PositiveRadius → ℝ) (𝓝[>] (0 : ℝ)) := positiveRadius_atBot_eq
  have hsame := (density_characterization hn data.2.2 data.1 data.2.1 b).2.2.2
    (density hn hmin hu hN c) (by rw [← hfilter]; exact hscaled)
  exact hsame.symm

end StratificationTheory
