module

public import StratificationTheory.Foundation.SobolevRadialL2Bound
public import StratificationTheory.Foundation.AnnularRadialRigidity

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology BigOperators

namespace StratificationTheory

/-- Vanishing normalized radial columns off the center implies vanishing
unnormalized radial sums on the whole ambient measure space. At the center the
literal sum is zero. -/
theorem raw_radial_columns_ae_zero_of_radial_columns_zero {n q : ℕ}
    (Du : Domain n → Gradient n q) (a : Domain n)
    (hrad : ∀ᵐ x ∂volume.restrict ({a}ᶜ),
      ‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i = 0) :
    ∀ᵐ x ∂volume, ∑ i : Fin n, (x - a) i • Du x i = 0 := by
  have h := (ae_restrict_iff' (measurableSet_singleton a).compl).mp hrad
  filter_upwards [h] with x hx
  by_cases hxa : x = a
  · subst x
    simp only [sub_self, WithLp.ofLp_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · have hnorm : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
    have hzero := hx (by simpa only [mem_compl_iff, mem_singleton_iff] using hxa)
    have hmul := congrArg (fun v : Ambient q => ‖x - a‖ • v) hzero
    simpa only [smul_smul, mul_inv_cancel₀ hnorm, one_smul, smul_zero] using hmul

/-- An actual globally local Sobolev map with zero radial weak-gradient sums
is invariant almost everywhere under every positive centered dilation. -/
theorem ae_eq_rescale_of_raw_radial_zero {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du) (a : Domain n)
    (hraw : ∀ᵐ x ∂volume, ∑ i : Fin n, (x - a) i • Du x i = 0)
    {l : ℝ} (hl : 0 < l) :
    (fun x => u (a + l • (x - a))) =ᵐ[volume] u := by
  have hball (r : ℝ) (hr : 0 < r) :
      (fun x => u (a + l • (x - a))) =ᵐ[volume.restrict (Metric.ball a r)] u := by
    let R := max 1 l * r + 1
    have hmargin : max 1 l * r < R := by dsimp [R]; linarith
    have hwu : MemW12 (ballDomain a R) u Du := hu.memW12_ball (subset_univ _)
    have henergy := memW12_radial_L2_square_le a hr hl hmargin hwu
    have hzero : (∫ x in Metric.ball a R, ‖∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_of_ae hraw] with x hx
      simp only [hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]
    rw [hzero, mul_zero] at henergy
    have huInner : MemLp u 2 (volume.restrict (Metric.ball a r)) :=
      (hu.memW12_ball (a := a) (r := r) (subset_univ _)).2.1
    have huScale : MemLp (fun x => u (a + l • (x - a))) 2
        (volume.restrict (Metric.ball a r)) := by
      have hL := memLp_affineBall a a hl (l * r)
        (hu.memW12_ball (a := a) (r := l * r) (subset_univ _)).2.1
      simpa only [mul_div_cancel_left₀ _ hl.ne'] using hL
    have hI := (huScale.sub huInner).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    have hnonneg : ∀ᵐ x ∂volume.restrict (Metric.ball a r),
        0 ≤ ‖u (a + l • (x - a)) - u x‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    have hnull : (∫ x in Metric.ball a r, ‖u (a + l • (x - a)) - u x‖ ^ 2) = 0 :=
      le_antisymm henergy (integral_nonneg fun _ => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hI).mp hnull
    filter_upwards [hae] with x hx
    exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hx))
  have hballs : ∀ k : ℕ, (fun x => u (a + l • (x - a))) =ᵐ[
      volume.restrict (Metric.ball a ((k : ℝ) + 1))] u := fun k => hball _ (by positivity)
  have hwhole := (ae_eq_restrict_iUnion_iff (fun k : ℕ => Metric.ball a ((k : ℝ) + 1))
    (fun x => u (a + l • (x - a))) u).mpr hballs
  simpa only [Metric.iUnion_ball_nat_succ, Measure.restrict_univ] using hwhole

end StratificationTheory

namespace HarmonicMaps

/-- A globally defined local minimizer with constant finite real normalized
energy is invariant almost everywhere under every positive centered dilation.
The radial zero field is produced by the actual monotonicity formula. -/
theorem IsLocallyEnergyMinimizing.ae_eq_rescale_of_constant_energy {n q : ℕ}
    (hn : 2 ≤ n) {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (a : Domain n) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du a r).toReal = θ)
    {l : ℝ} (hl : 0 < l) :
    (fun x => u (a + l • (x - a))) =ᵐ[volume] u := by
  have hrad := hmin.radialColumns_ae_zero_of_constant_energy hn hu hN a θ henergy
  have hraw := StratificationTheory.raw_radial_columns_ae_zero_of_radial_columns_zero Du a hrad
  exact StratificationTheory.ae_eq_rescale_of_raw_radial_zero hu a hraw hl


end HarmonicMaps
