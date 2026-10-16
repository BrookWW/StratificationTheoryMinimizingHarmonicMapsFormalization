module

public import StratificationTheory.Compactness.SmoothTranslationBound
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.L2TranslationContinuity
public import HarmonicMaps.Analysis.VariableMollificationL2

/-!
# Quantitative Sobolev translations

The original displayed weak gradient controls the squared L2 translation error
on interior concentric balls. The estimate follows from simultaneous smooth
density, the smooth segment estimate and Lebesgue translation invariance.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology BigOperators

namespace StratificationTheory.Compactness

private theorem add_mem_outer_ball {n : ℕ} {a x v : Domain n} {r R : ℝ}
    (hmargin : r + ‖v‖ < R) (hx : x ∈ Metric.ball a r) : x + v ∈ Metric.ball a R := by
  have hdist : dist (x + v) a ≤ dist x a + ‖v‖ := by
    rw [dist_eq_norm, dist_eq_norm, show x + v - a = (x - a) + v by abel]
    exact norm_add_le (x - a) v
  exact hdist.trans_lt ((add_lt_add_of_lt_of_le hx (le_refl ‖v‖)).trans hmargin)

private theorem shifted_memLp_ball {n q : ℕ} {a v : Domain n} {r R : ℝ}
    (hmargin : r + ‖v‖ < R) {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    MemLp (fun x => f (x + v)) 2 (volume.restrict (Metric.ball a r)) := by
  have hz := (memLp_zeroExtension measurableSet_ball hf).comp_measurePreserving
    (measurePreserving_add_right volume v)
  have heq : (fun x => (Metric.ball a R).indicator f (x + v)) =ᵐ[volume.restrict (Metric.ball a r)]
      (fun x => f (x + v)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact indicator_of_mem (add_mem_outer_ball hmargin hx) f
  exact (memLp_congr_ae heq).mp (hz.mono_measure Measure.restrict_le_self)

private theorem shifted_eLpNorm_ball_le {n q : ℕ} {a v : Domain n} {r R : ℝ}
    (hmargin : r + ‖v‖ < R) {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    eLpNorm (fun x => f (x + v)) 2 (volume.restrict (Metric.ball a r)) ≤
      eLpNorm f 2 (volume.restrict (Metric.ball a R)) := by
  have heq : (fun x => f (x + v)) =ᵐ[volume.restrict (Metric.ball a r)]
      (fun x => (Metric.ball a R).indicator f (x + v)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (indicator_of_mem (add_mem_outer_ball hmargin hx) f).symm
  rw [eLpNorm_congr_ae heq]
  calc
    _ ≤ eLpNorm (fun x => (Metric.ball a R).indicator f (x + v)) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm ((Metric.ball a R).indicator f) 2 volume := by
      simpa only [Function.comp_def] using
        eLpNorm_comp_measurePreserving (p := 2) (μ := volume) (ν := volume)
          (f := fun x : Domain n => x + v) (g := (Metric.ball a R).indicator f)
          (memLp_zeroExtension measurableSet_ball hf).aestronglyMeasurable
          (measurePreserving_add_right volume v)
    _ = eLpNorm f 2 (volume.restrict (Metric.ball a R)) := by
      exact eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball

private theorem tendsto_integral_norm_sq_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ^ 2 ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  have hn := hLp.norm.pow 2
  have heq (k : ℕ) := integral_norm_sq_eq_eLpNorm_two_toReal_sq (hf k)
  have huEq := integral_norm_sq_eq_eLpNorm_two_toReal_sq hu
  simpa only [Lp.norm_toLp, ← heq, ← huEq] using hn

/-- A weak Sobolev map has a uniform quantitative L2 translation estimate on
any interior concentric ball. The gradient is the original displayed field. -/
theorem memW12_translation_L2_square_le {n q : ℕ}
    (a : Domain n) {r R : ℝ} (hR : 0 < R) (v : Domain n)
    (hmargin : r + ‖v‖ < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) :
    (∫ x in Metric.ball a r, ‖u (x + v) - u x‖ ^ 2) ≤
      ‖v‖ ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
  obtain ⟨m, hm, hmW, hconv, hDconv⟩ := hu.smoothDensity_memW12_ball hR
  have hrR : r ≤ R := (lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg v)) hmargin).le
  have hmu (k : ℕ) : MemLp (m k) 2 (volume.restrict (Metric.ball a r)) :=
    ((hmW k).2.1).mono_measure (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR))
  have huInner := hu.2.1.mono_measure (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR))
  have hmDiff (k : ℕ) : MemLp (fun x => m k (x + v) - m k x) 2
      (volume.restrict (Metric.ball a r)) :=
    (shifted_memLp_ball hmargin (hmW k).2.1).sub (hmu k)
  have huDiff : MemLp (fun x => u (x + v) - u x) 2 (volume.restrict (Metric.ball a r)) :=
    (shifted_memLp_ball hmargin hu.2.1).sub huInner
  have hDiffConv : Tendsto (fun k => eLpNorm
      ((fun x => m k (x + v) - m k x) - (fun x => u (x + v) - u x)) 2
      (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := by
    have htwice : Tendsto (fun k => eLpNorm (m k - u) 2
        (volume.restrict (Metric.ball a R)) + eLpNorm (m k - u) 2
        (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
      simpa only [add_zero] using hconv.add hconv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htwice
      (fun _ => zero_le)
    intro k
    have heq : ((fun x => m k (x + v) - m k x) - (fun x => u (x + v) - u x)) =
        (fun x => (m k - u) (x + v)) - (m k - u) := by
      funext x
      simp only [Pi.sub_apply]
      abel
    dsimp only
    rw [heq]
    exact (eLpNorm_sub_le (shifted_memLp_ball hmargin ((hmW k).2.1.sub hu.2.1)).aestronglyMeasurable
      ((hmu k).sub huInner).aestronglyMeasurable (by norm_num)).trans
      (add_le_add (shifted_eLpNorm_ball_le hmargin ((hmW k).2.1.sub hu.2.1))
        (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR))))
  have hleft := tendsto_integral_norm_sq_of_L2 hmDiff huDiff hDiffConv
  have hcolumns (i : Fin n) := tendsto_integral_norm_sq_of_L2
    (fun k => (hmW k).2.2 i) (hu.2.2 i) (hDconv i)
  have hsum := tendsto_finsetSum Finset.univ fun i _ => hcolumns i
  have henergy : Tendsto (fun k => ∫ x in Metric.ball a R,
      hsNormSq (fun i => coordinateDerivative (m k) (hm k) i x)) atTop
      (𝓝 (∫ x in Metric.ball a R, hsNormSq (Du x))) := by
    have hmE (k : ℕ) : (∫ x in Metric.ball a R,
        hsNormSq (fun i => coordinateDerivative (m k) (hm k) i x)) =
        ∑ i : Fin n, ∫ x in Metric.ball a R, ‖coordinateDerivative (m k) (hm k) i x‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun i _ => ((hmW k).2.2 i).integrable_norm_pow (by decide))
    have huE : (∫ x in Metric.ball a R, hsNormSq (Du x)) =
        ∑ i : Fin n, ∫ x in Metric.ball a R, ‖Du x i‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun i _ => (hu.2.2 i).integrable_norm_pow (by decide))
    simpa only [hmE, huE, ballDomain] using hsum
  exact le_of_tendsto_of_tendsto hleft (henergy.const_mul (‖v‖ ^ 2))
    (Filter.Eventually.of_forall fun k => smooth_translation_L2_square_le a v hmargin (hm k)
      (fun i => (hmW k).2.2 i))

end StratificationTheory.Compactness
