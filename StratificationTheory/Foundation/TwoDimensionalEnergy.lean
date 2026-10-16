module

public import StratificationTheory.Foundation.PositiveRadiusLimits
public import StratificationTheory.Foundation.EnergyRadiusContinuity
public import StratificationTheory.Foundation.SmoothRepresentativeNeighborhoods
public import StratificationTheory.Foundation.RegularPointNeighborhoods

/-!
# Two-dimensional normalized energy

Absolute continuity of the actual finite energy integral makes normalized
energy tend to zero at every interior point in dimension two. The imported
uniform small-energy theorem then supplies a local smooth a.e. representative
for each minimizing map. No Hausdorff dimension assertion is used.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ContDiff

namespace HarmonicMaps

theorem MemW12Loc.normalizedEnergy_tendsto_zero_two_dimensional {q : ℕ}
    {Ω : OpenDomain 2} {u : Domain 2 → Ambient q} {Du : Domain 2 → Gradient 2 q}
    (hu : MemW12Loc Ω u Du) (a : Domain 2) (ha : a ∈ Ω.val) :
    Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
      atBot (𝓝 (0 : ℝ)) := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds ha)
  have hcont := hu.continuousOn_dirichletEnergy_toReal_ball_radii
    (by norm_num : 0 < 2) hR.le hball
  have hwithin : Tendsto (fun r : PositiveRadius => r.val) atBot (𝓝[Icc 0 R] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨StratificationTheory.positiveRadius_val_tendsto_zero, ?_⟩
    filter_upwards [eventually_le_atBot (⟨R, hR⟩ : PositiveRadius)] with r hr
    exact ⟨r.property.le, hr⟩
  have hconv := (hcont 0 ⟨le_rfl, hR.le⟩).tendsto.comp hwithin
  have hzero : (dirichletEnergy Du (Metric.ball a 0)).toReal = 0 := by
    simp only [Metric.ball_zero, dirichletEnergy, setLIntegral_empty, ENNReal.toReal_zero]
  rw [hzero] at hconv
  apply hconv.congr
  intro r
  unfold normalizedEnergy
  norm_num only
  simp only [zpow_zero, ENNReal.ofReal_one, one_mul]
  rfl

end HarmonicMaps

namespace StratificationTheory

theorem exists_smooth_representative_two_dimensional {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 2)
    (u : Domain 2 → Ambient q) (Du : Domain 2 → Gradient 2 q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (a : Domain 2) (ha : a ∈ Ω.val) :
    ∃ U : OpenDomain 2, a ∈ U.val ∧ U.val ⊆ Ω.val ∧
      ∃ f : Domain 2 → Ambient q, ContDiffOn ℝ ∞ f U.val ∧
        u =ᵐ[volume.restrict U.val] f ∧ ∀ x ∈ U.val, f x ∈ N.carrierSet := by
  obtain ⟨ε, hε, hthreshold⟩ := exists_uniform_threshold_for_smooth_rep (by norm_num : 2 ≤ 2) N
  exact hthreshold Ω u Du hu hN hmin a ha 0
    (hu.normalizedEnergy_tendsto_zero_two_dimensional a ha) hε

theorem isRegularPoint_two_dimensional {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 2)
    (u : Domain 2 → Ambient q) (Du : Domain 2 → Gradient 2 q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (a : Ω.val) :
    IsRegularPoint Ω u a := by
  obtain ⟨U, ha, hU, w, hw, huw, _hwN⟩ :=
    exists_smooth_representative_two_dimensional N Ω u Du hu hN hmin a.val a.property
  exact (isRegularPoint_iff_exists_open_neighborhood Ω u a).mpr
    ⟨U, ha, hU, w, hw, huw.symm⟩

theorem singularSet_eq_empty_two_dimensional {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 2)
    (u : Domain 2 → Ambient q) (Du : Domain 2 → Gradient 2 q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) :
    singularSet Ω u = ∅ := by
  ext a
  constructor
  · intro ha
    exact False.elim (ha (isRegularPoint_two_dimensional N Ω u Du hu hN hmin a))
  · intro ha
    exact False.elim ha

end StratificationTheory
