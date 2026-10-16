module

public import StratificationTheory.Foundation.EnergyRadiusContinuity
public import HarmonicMaps.Analysis.L2TranslationContinuity
public import HarmonicMaps.Analysis.AffineBallMeasure
import HolderToCK.Analysis.Harmonic.ReplacementLimits

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace StratificationTheory

/-- Actual global L2 translation continuity makes the square integral on a
fixed ball continuous at zero displacement. -/
theorem continuousAt_integral_norm_sq_translation_ball {n q : ℕ}
    {f : Domain n → Ambient q} (hf : MemLp f 2 volume) (a : Domain n) (r : ℝ) :
    ContinuousAt (fun v : Domain n => ∫ x in Metric.ball a r, ‖f (x - v)‖ ^ 2) 0 := by
  have hfv (v : Domain n) : MemLp (fun x => f (x - v)) 2 (volume.restrict (Metric.ball a r)) :=
    (hf.comp_measurePreserving (measurePreserving_sub_right volume v)).mono_measure Measure.restrict_le_self
  have hf0 : MemLp f 2 (volume.restrict (Metric.ball a r)) := hf.mono_measure Measure.restrict_le_self
  have hconv : Tendsto (fun v : Domain n => eLpNorm ((fun x => f (x - v)) - f) 2
      (volume.restrict (Metric.ball a r))) (𝓝 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_translation_sub hf) (fun _ => zero_le)
    intro v
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun v x => f (x - v)) hfv f hf0).mpr hconv
  have hn := hLp.norm.pow 2
  change Tendsto _ (𝓝 (0 : Domain n)) (𝓝 _)
  simpa only [← HolderToCK.integral_norm_sq_eq_L2_norm_sq, sub_zero] using hn

end StratificationTheory

namespace HarmonicMaps

/-- On a fixed admissible positive radius, finite real Dirichlet energy is
continuous as the center varies. Actual L2 translation of the displayed
columns supplies the continuity. -/
theorem MemW12Loc.continuousAt_dirichletEnergy_toReal_center {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a₀ : Domain n} {R : ℝ}
    (hball : Metric.closedBall a₀ R ⊆ Ω.val) (r : PositiveRadius) (hrR : r.val < R) :
    ContinuousAt (fun a : Domain n => (dirichletEnergy Du (Metric.ball a r.val)).toReal) a₀ := by
  let g : Fin n → Domain n → Ambient q := fun i => (Metric.ball a₀ R).indicator (fun x => Du x i)
  have hg (i : Fin n) : MemLp (g i) 2 volume :=
    memLp_zeroExtension measurableSet_ball ((hu.memW12_ball hball).2.2 i)
  have hc (i : Fin n) : ContinuousAt (fun a : Domain n =>
      ∫ x in Metric.ball a₀ r.val, ‖g i (x - (a₀ - a))‖ ^ 2) a₀ := by
    have hzero : Tendsto (fun a : Domain n => a₀ - a) (𝓝 a₀) (𝓝 (0 : Domain n)) := by
      have hc : Continuous (fun a : Domain n => a₀ - a) := by fun_prop
      simpa only [sub_self] using hc.tendsto a₀
    have hi := (StratificationTheory.continuousAt_integral_norm_sq_translation_ball (hg i) a₀ r.val).tendsto.comp hzero
    change Tendsto _ (𝓝 a₀) (𝓝 _)
    simpa only [Function.comp_def, sub_self, sub_zero] using hi
  have hsum : ContinuousAt (fun a : Domain n => ∑ i : Fin n,
      ∫ x in Metric.ball a₀ r.val, ‖g i (x - (a₀ - a))‖ ^ 2) a₀ := by
    change Tendsto _ (𝓝 a₀) (𝓝 _)
    exact tendsto_finsetSum Finset.univ (fun i _ => (hc i).tendsto)
  have heq : (fun a : Domain n => (dirichletEnergy Du (Metric.ball a r.val)).toReal) =ᶠ[𝓝 a₀]
      (fun a : Domain n => ∑ i : Fin n, ∫ x in Metric.ball a₀ r.val, ‖g i (x - (a₀ - a))‖ ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds a₀ (sub_pos.mpr hrR)] with a ha
    have hdist : dist a a₀ < R - r.val := Metric.mem_ball.mp ha
    have hinside : r.val + dist a a₀ ≤ R := by linarith only [hdist]
    have haball : Metric.closedBall a r.val ⊆ Ω.val :=
      (Metric.closedBall_subset_closedBall' hinside).trans hball
    rw [dirichletEnergy_toReal (hu.integrable_hsNormSq_ball haball)]
    have htransport := integral_affineBall a a₀ (by norm_num : (0 : ℝ) < 1) r.val
      (fun x => hsNormSq (Du x))
    simp only [div_one, one_pow, inv_one, one_smul] at htransport
    rw [← htransport]
    have hfunc : (fun x => hsNormSq (Du (a + (x - a₀)))) =ᵐ[
        volume.restrict (Metric.ball a₀ r.val)]
        (fun x => ∑ i : Fin n, ‖g i (x - (a₀ - a))‖ ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hxarg : x - (a₀ - a) = a + (x - a₀) := by abel
      have hxball : a + (x - a₀) ∈ Metric.ball a r.val := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hxlarge : a + (x - a₀) ∈ Metric.ball a₀ R :=
        (Metric.ball_subset_ball' hinside) hxball
      unfold hsNormSq
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp only [g]
      rw [hxarg, indicator_of_mem hxlarge]
    rw [integral_congr_ae hfunc]
    exact integral_finsetSum Finset.univ (fun i _ =>
      (((hg i).comp_measurePreserving (measurePreserving_sub_right volume (a₀ - a))).mono_measure
        Measure.restrict_le_self).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  exact hsum.congr_of_eventuallyEq heq

/-- At a fixed positive radius with an admissible larger ball, finite real
normalized energy is continuous in its center. -/
theorem MemW12Loc.continuousAt_normalizedEnergy_toReal_center {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a₀ : Domain n} {R : ℝ}
    (hball : Metric.closedBall a₀ R ⊆ Ω.val) (r : PositiveRadius) (hrR : r.val < R) :
    ContinuousAt (fun a : Domain n => (normalizedEnergy Du a r).toReal) a₀ := by
  have hc := (hu.continuousAt_dirichletEnergy_toReal_center hball r hrR).const_mul
    (r.val ^ (2 - (n : ℤ)))
  have hformula : (fun a : Domain n => (normalizedEnergy Du a r).toReal) =
      (fun a : Domain n => r.val ^ (2 - (n : ℤ)) *
        (dirichletEnergy Du (Metric.ball a r.val)).toReal) := by
    funext a
    unfold normalizedEnergy
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (zpow_pos r.property _))]
  rw [hformula]
  exact hc

end HarmonicMaps
