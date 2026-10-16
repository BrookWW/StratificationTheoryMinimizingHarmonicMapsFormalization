module

public import StratificationTheory.Foundation.NormalizedEnergyOrder

public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace HarmonicMaps

/-- Equal normalized energies at two admissible radii force the actual radial
weak-gradient columns to vanish almost everywhere on the intervening annulus. -/
theorem IsLocallyEnergyMinimizing.radialColumns_ae_zero_of_equal_energy {n q : ℕ}
    (hn : 2 ≤ n) {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R s r : ℝ}
    (hR : 0 < R) (hball : Metric.closedBall a R ⊆ Ω.val)
    (hs : 0 < s) (hsr : s < r) (hrR : r ≤ R)
    (heq : normalizedEnergy Du a ⟨s, hs⟩ = normalizedEnergy Du a ⟨r, hs.trans hsr⟩) :
    ∀ᵐ x ∂volume.restrict (Metric.ball a r \ Metric.ball a s),
      ‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i = 0 := by
  obtain ⟨hI, hincrement, _horder⟩ := hmin.monotonicity hn hu hN hR hball hs hsr hrR
  have hzero : (∫ x in Metric.ball a r \ Metric.ball a s,
      ‖x - a‖ ^ (2 - (n : ℤ)) *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) = 0 := by
    rw [heq, sub_self] at hincrement
    exact (mul_eq_zero.mp hincrement.symm).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hnonneg : ∀ᵐ x ∂volume.restrict (Metric.ball a r \ Metric.ball a s),
      0 ≤ ‖x - a‖ ^ (2 - (n : ℤ)) *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2 :=
    Eventually.of_forall fun x => mul_nonneg (zpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hI).mp hzero
  filter_upwards [hae, ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with x hx hxA
  have hxa : x ≠ a := by
    intro h
    have hmem : x ∈ Metric.ball a s := by simpa only [h] using Metric.mem_ball_self hs
    exact hxA.2 hmem
  have hnorm : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
  have hradial : ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hx).resolve_left (zpow_pos hnorm _).ne'
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hradial)

/-- A globally defined local minimizer with constant normalized energy at
all centered balls has vanishing actual radial columns almost everywhere
outside its center. Countably many annuli cover the punctured domain. -/
theorem IsLocallyEnergyMinimizing.radialColumns_ae_zero_of_constant_energy {n q : ℕ}
    (hn : 2 ≤ n) {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (a : Domain n) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du a r).toReal = θ) :
    ∀ᵐ x ∂volume.restrict ({a}ᶜ),
      ‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i = 0 := by
  let A : ℕ → Set (Domain n) := fun k =>
    Metric.ball a ((k : ℝ) + 2) \ Metric.ball a (1 / ((k : ℝ) + 2))
  have hr (k : ℕ) : 0 < (k : ℝ) + 2 := by positivity
  have hs (k : ℕ) : 0 < 1 / ((k : ℝ) + 2) := one_div_pos.mpr (hr k)
  have hsr (k : ℕ) : 1 / ((k : ℝ) + 2) < (k : ℝ) + 2 := by
    have hkle : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    apply (div_lt_iff₀ (hr k)).mpr
    nlinarith only [hkle]
  have hA (k : ℕ) : ∀ᵐ x ∂volume.restrict (A k),
      ‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i = 0 := by
    apply hmin.radialColumns_ae_zero_of_equal_energy hn hu hN (hr k)
      (subset_univ _) (hs k) (hsr k) le_rfl
    have hsfinite := hu.normalizedEnergy_ne_top_ball
      (a := a) (r := (⟨1 / ((k : ℝ) + 2), hs k⟩ : PositiveRadius)) (subset_univ _)
    have hrfinite := hu.normalizedEnergy_ne_top_ball
      (a := a) (r := (⟨(k : ℝ) + 2, hr k⟩ : PositiveRadius)) (subset_univ _)
    apply (ENNReal.toReal_eq_toReal_iff' hsfinite hrfinite).mp
    exact (henergy ⟨_, hs k⟩).trans (henergy ⟨_, hr k⟩).symm
  have hcover : (⋃ k : ℕ, A k) = {a}ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      intro hxa
      have heq : x = a := mem_singleton_iff.mp hxa
      have hxinner : x ∈ Metric.ball a (1 / ((k : ℝ) + 2)) := by
        simpa only [heq] using Metric.mem_ball_self (hs k)
      exact hk.2 hxinner
    · intro hx
      have hxa : x ≠ a := fun h => hx (mem_singleton_iff.mpr h)
      have hd : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
      obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x - a‖ (1 / ‖x - a‖))
      have houter : ‖x - a‖ < (k : ℝ) + 2 :=
        (lt_of_le_of_lt (le_max_left _ _) hk).trans (by linarith)
      have hinner : 1 / ((k : ℝ) + 2) ≤ ‖x - a‖ := by
        have hrecip : 1 / ‖x - a‖ < (k : ℝ) + 2 :=
          (lt_of_le_of_lt (le_max_right _ _) hk).trans (by linarith)
        apply (div_le_iff₀ (hr k)).mpr
        have := (div_lt_iff₀ hd).mp hrecip
        linarith only [this]
      apply mem_iUnion.mpr
      refine ⟨k, ?_, ?_⟩
      · exact Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using houter)
      · exact fun h => (not_lt.mpr hinner) (by simpa only [dist_eq_norm] using Metric.mem_ball.mp h)
  rw [← hcover]
  exact (ae_restrict_iUnion_iff A _).mpr hA

end HarmonicMaps
