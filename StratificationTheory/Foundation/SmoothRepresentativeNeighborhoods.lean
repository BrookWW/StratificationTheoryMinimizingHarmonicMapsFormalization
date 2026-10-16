module

public import StratificationTheory.Foundation.SmoothNormalizedEnergy
public import HarmonicMaps.SobolevRestriction
public import HolderToCK.Frozen.SmallEnergySmoothRegularity

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ContDiff

namespace StratificationTheory

/-- The existence of a smooth almost-everywhere representative on an open
neighborhood defines an open set of ambient points. -/
theorem isOpen_setOf_exists_contDiffOn_representative {n q : ℕ}
    (Ω : OpenDomain n) (u : Domain n → Ambient q) :
    IsOpen {a : Domain n | ∃ U : OpenDomain n, a ∈ U.val ∧ U.val ⊆ Ω.val ∧
      ∃ f : Domain n → Ambient q, ContDiffOn ℝ ∞ f U.val ∧
        u =ᵐ[volume.restrict U.val] f} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro a ⟨U, haU, hUΩ, f, hf, huf⟩
  exact mem_of_superset (U.property.mem_nhds haU) fun b hb =>
    ⟨U, hb, hUΩ, f, hf, huf⟩

/-- A weak Sobolev map with a C1 representative on an actual open neighborhood
has zero limiting normalized energy there. -/
theorem normalizedEnergy_tendsto_zero_of_local_contDiffOn_rep {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (a : Domain n)
    (hrep : ∃ U : OpenDomain n, a ∈ U.val ∧ U.val ⊆ Ω.val ∧
      ∃ f : Domain n → Ambient q, ContDiffOn ℝ 1 f U.val ∧
        u =ᵐ[volume.restrict U.val] f) :
    Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
      atBot (𝓝 (0 : ℝ)) := by
  obtain ⟨U, haU, hUΩ, f, hf, huf⟩ := hrep
  exact (hu.mono hUΩ).normalizedEnergy_tendsto_zero_of_contDiffOn_rep hf huf a haU

/-- A single threshold depending only on dimension and target applies to
all actual finite normalized-energy limits. A limit strictly below it supplies
a smooth representative on an open neighborhood of the center. -/
theorem exists_uniform_threshold_for_smooth_rep {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du → TakesValuesIn N Ω u →
        IsLocallyEnergyMinimizing N Ω u Du →
        ∀ (a : Domain n), a ∈ Ω.val → ∀ θ : ℝ,
          Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
            atBot (𝓝 θ) → θ < ε →
          ∃ U : OpenDomain n, a ∈ U.val ∧ U.val ⊆ Ω.val ∧
            ∃ f : Domain n → Ambient q, ContDiffOn ℝ ∞ f U.val ∧
              u =ᵐ[volume.restrict U.val] f ∧
              ∀ x ∈ U.val, f x ∈ N.carrierSet := by
  obtain ⟨ε, γ, C, hε, _hγ, _hγOne, hsmall⟩ := HolderToCK.smallEnergySmoothRegularity hn N
  refine ⟨ε, hε, ?_⟩
  intro Ω u Du hu hN hmin a ha θ hθ hθε
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds ha)
  have hevent : ∀ᶠ r : PositiveRadius in atBot, (normalizedEnergy Du a r).toReal < ε :=
    hθ.eventually (gt_mem_nhds hθε)
  obtain ⟨r, hrR, hrsmall⟩ := ((eventually_le_atBot (⟨R, hR⟩ : PositiveRadius)).and hevent).exists
  have hrball : Metric.closedBall a r.val ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall hrR).trans hball
  have hrsmallENN : normalizedEnergy Du a r ≤ ENNReal.ofReal ε :=
    (ENNReal.le_ofReal_iff_toReal_le (hu.normalizedEnergy_ne_top_ball hrball) hε.le).mpr
      hrsmall.le
  obtain ⟨w, hw, hwrep, hwN, _hwosc, _hwderiv, _hwHolder, _hwUnique⟩ :=
    hsmall Ω u Du hu hN hmin a r hrball hrsmallENN
  have hUΩ : Metric.ball a (r.val / 2) ⊆ Ω.val :=
    (Metric.ball_subset_ball (half_le_self r.property.le)).trans
      (Metric.ball_subset_closedBall.trans hrball)
  refine ⟨ballDomain a (r.val / 2), Metric.mem_ball_self (half_pos r.property), hUΩ,
    w, hw, ?_, hwN⟩
  filter_upwards [hwrep.2, ae_restrict_mem measurableSet_ball] with x hx hxb
  exact (hx hxb).symm

end StratificationTheory
