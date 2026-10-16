/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.Frozen.RegularPoint

import StratificationTheory.Foundation.SmoothRepresentativeNeighborhoods
import StratificationTheory.Foundation.RegularPointNeighborhoods

/-!
# Density and local smooth representatives

Smooth representatives at regular points force the actual density to vanish.
The imported small-energy smooth regularity theorem supplies a positive
threshold depending only on dimension and target below which actual density
implies regularity.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ContDiff

namespace StratificationTheory

/-- Regularity of the map, through a local smooth a.e. representative,
forces its actual weak-gradient density to vanish. -/
theorem density_eq_zero_of_isRegularPoint {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) (hreg : IsRegularPoint Ω u a) :
    density hn hmin hu hN a = 0 := by
  obtain ⟨U, haU, hUΩ, w, hw, hwu⟩ :=
    (isRegularPoint_iff_exists_open_neighborhood Ω u a).mp hreg
  have hzero := normalizedEnergy_tendsto_zero_of_local_contDiffOn_rep hu.1 a.val
    ⟨U, haU, hUΩ, w, hw.of_le (by norm_num), hwu.symm⟩
  exact tendsto_nhds_unique (normalizedEnergy_tendsto_density_atBot hn hmin hu hN a) hzero

/-- The threshold precedes the domain and map quantifiers, so one positive
constant works for every locally minimizing map into the fixed target. -/
theorem exists_uniform_density_threshold_for_isRegularPoint {n q : ℕ}
    (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
        (hN : TakesValuesIn N Ω u) (a : Ω.val),
        density hn hmin hu hN a < ε → IsRegularPoint Ω u a := by
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_threshold_for_smooth_rep hn N
  refine ⟨ε, hε, ?_⟩
  intro Ω u Du hmin hu hN a hdensity
  obtain ⟨U, haU, hUΩ, w, hw, huw, _hwN⟩ :=
    hsmall Ω u Du hu hN hmin a.val a.property (density hn hmin hu hN a)
      (normalizedEnergy_tendsto_density_atBot hn hmin hu hN a) hdensity
  exact (isRegularPoint_iff_exists_open_neighborhood Ω u a).mpr
    ⟨U, haU, hUΩ, w, hw, huw.symm⟩

end StratificationTheory
