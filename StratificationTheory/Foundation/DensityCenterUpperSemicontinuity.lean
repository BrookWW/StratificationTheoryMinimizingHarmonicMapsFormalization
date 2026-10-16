/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Foundation.DensityBounds
public import Mathlib.Topology.Semicontinuity.Basic

import StratificationTheory.Foundation.MovingCenterEnergyContinuity

/-!
# Upper semicontinuity of density in its center

For a fixed locally minimizing Sobolev map, finite normalized energy on a
fixed inner ball varies continuously with the center. Density is bounded
above by each of these energies and approaches them as the radius shrinks.
Consequently the actual density function on the open-domain subtype is
upper semicontinuous, and its superlevel sets are relatively closed.
-/

public section

open HarmonicMaps Filter Set
open scoped Topology

namespace StratificationTheory

/-- Density of a fixed map is upper semicontinuous on its actual domain.
The topology is the subtype topology on the open domain. -/
theorem upperSemicontinuous_density {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) :
    UpperSemicontinuous (density hn hmin hu hN) := by
  intro a η hη
  obtain ⟨R, hR, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds a.property)
  obtain ⟨r, hrR, _hrball, hrη⟩ := exists_small_radius_energy_lt_of_density_lt
    hn hmin hu hN a ⟨R, hR⟩ hball hη
  have hc : ContinuousAt (fun b : Ω.val => (normalizedEnergy Du b.val r).toReal) a :=
    (hu.continuousAt_normalizedEnergy_toReal_center hball r hrR).comp
      continuous_subtype_val.continuousAt
  have henergy : ∀ᶠ b : Ω.val in 𝓝 a, (normalizedEnergy Du b.val r).toReal < η :=
    hc.tendsto.eventually (gt_mem_nhds hrη)
  have hnear : ∀ᶠ b : Ω.val in 𝓝 a, dist b.val a.val < R - r.val := by
    exact continuous_subtype_val.continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds a.val (sub_pos.mpr hrR))
  filter_upwards [henergy, hnear] with b hbenergy hbnear
  have hbouter : Metric.closedBall b.val r.val ⊆ Ω.val := by
    apply (Metric.closedBall_subset_closedBall' ?_).trans hball
    linarith only [hbnear]
  exact (density_le_normalizedEnergy_toReal hn hmin hu hN b r hbouter).trans_lt hbenergy

/-- For a fixed map, every density superlevel set is relatively closed in
the open domain. -/
theorem isClosed_density_superlevel {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (η : ℝ) :
    IsClosed {a : Ω.val | η ≤ density hn hmin hu hN a} :=
  (upperSemicontinuous_density hn hmin hu hN).isClosed_preimage η

end StratificationTheory
