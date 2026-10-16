/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Frozen.DensityCharacterization

import StratificationTheory.Foundation.NormalizedEnergyOrder
import StratificationTheory.Foundation.PositiveRadiusLimits

/-!
# Bounds for the actual finite density

The registered density is nonnegative, is the limit along positive radii,
and is bounded by the finite real normalized energy on every admissible ball.
A strict upper bound for density can be realized on an arbitrarily small
admissible positive radius.
-/

public section

open HarmonicMaps Filter Set
open scoped Topology

namespace StratificationTheory

theorem density_nonneg {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) :
    0 ≤ density hn hmin hu hN a :=
  (density_characterization hn hmin hu hN a).1

/-- The positive-radius order filter is the same one-sided radius filter
used in the registered density characterization. -/
theorem normalizedEnergy_tendsto_density_atBot {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) :
    Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a.val r).toReal)
      atBot (𝓝 (density hn hmin hu hN a)) := by
  have hfilter : (atBot : Filter PositiveRadius) =
      comap (Subtype.val : PositiveRadius → ℝ) (𝓝[>] (0 : ℝ)) := positiveRadius_atBot_eq
  rw [hfilter]
  exact (density_characterization hn hmin hu hN a).2.1

/-- Density is bounded by the actual finite real energy at an admissible
positive radius, including the outer endpoint. -/
theorem density_le_normalizedEnergy_toReal {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) (r : PositiveRadius)
    (hball : Metric.closedBall a.val r.val ⊆ Ω.val) :
    density hn hmin hu hN a ≤ (normalizedEnergy Du a.val r).toReal := by
  apply le_of_tendsto (normalizedEnergy_tendsto_density_atBot hn hmin hu hN a)
  filter_upwards [eventually_le_atBot r] with s hs
  exact (hmin.normalizedEnergy_toReal_monotoneOn hn hu hN r.property hball)
    (show s.val ≤ r.val from hs) (show r.val ≤ r.val from le_rfl) hs

/-- Any real number strictly above density bounds the actual normalized
energy on some positive radius smaller than a prescribed admissible radius. -/
theorem exists_small_radius_energy_lt_of_density_lt {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) (R : PositiveRadius)
    (hball : Metric.closedBall a.val R.val ⊆ Ω.val) {η : ℝ}
    (hη : density hn hmin hu hN a < η) :
    ∃ r : PositiveRadius, r.val < R.val ∧
      Metric.closedBall a.val r.val ⊆ Ω.val ∧
      (normalizedEnergy Du a.val r).toReal < η := by
  have hevent := (normalizedEnergy_tendsto_density_atBot hn hmin hu hN a).eventually
    (gt_mem_nhds hη)
  obtain ⟨r, hr, henergy⟩ := ((eventually_le_atBot
    (⟨R.val / 2, half_pos R.property⟩ : PositiveRadius)).and hevent).exists
  have hrR : r.val < R.val := lt_of_le_of_lt hr (half_lt_self R.property)
  exact ⟨r, hrR, (Metric.closedBall_subset_closedBall hrR.le).trans hball, henergy⟩

end StratificationTheory
