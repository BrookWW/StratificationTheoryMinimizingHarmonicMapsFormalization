module

public import HarmonicMaps.Analysis.BallSegmentEnergy

public section

open MeasureTheory Set

namespace StratificationTheory

private theorem sq_unit_intervalIntegral_le {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, h t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (h t) ^ 2 := by
  let c := ∫ t in (0 : ℝ)..1, h t
  have hi : IntervalIntegrable h volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  have hsq : IntervalIntegrable (fun t => (h t) ^ 2) volume 0 1 :=
    (hcont.pow 2).intervalIntegrable_of_Icc zero_le_one
  have hexpand : (fun t => (h t - c) ^ 2) =
      (fun t => (h t) ^ 2 - (2 * c) * h t + c ^ 2) := by funext t; ring
  have hvariance : (∫ t in (0 : ℝ)..1, (h t - c) ^ 2) =
      (∫ t in (0 : ℝ)..1, (h t) ^ 2) - c ^ 2 := by
    rw [hexpand, intervalIntegral.integral_add (hsq.sub (hi.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_sub hsq (hi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    dsimp [c]
    ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    zero_le_one (fun t => sq_nonneg (h t - c))
  rw [hvariance] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- The squared endpoint difference on the unit interval is bounded by the
actual derivative's squared norm integral. -/
theorem unit_interval_energy_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f d : ℝ → E}
    (hd : ContinuousOn d (Icc (0 : ℝ) 1))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (d t) t) :
    ‖f 1 - f 0‖ ^ 2 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖d t‖ ^ 2 := by
  have hdi : IntervalIntegrable d volume 0 1 := hd.intervalIntegrable_of_Icc zero_le_one
  have hftc : (∫ t in (0 : ℝ)..1, d t) = f 1 - f 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hf t (by simpa only [uIcc_of_le zero_le_one] using ht)) hdi
  have hnorm : ‖f 1 - f 0‖ ≤ ∫ t in (0 : ℝ)..1, ‖d t‖ := by
    rw [← hftc]
    exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hsquare := pow_le_pow_left₀ (norm_nonneg (f 1 - f 0)) hnorm 2
  have hcs := sq_unit_intervalIntegral_le hd.norm
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact hsquare.trans hcs

end StratificationTheory
