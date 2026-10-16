module

public import StratificationTheory.Foundation.SmoothRadialL2Bound
public import StratificationTheory.Foundation.RadialGradientL2
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.AffineBallMeasure
import HolderToCK.Analysis.Harmonic.ReplacementLimits

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology BigOperators

namespace StratificationTheory

private theorem smooth_fderiv_apply_eq_sum {n q : ℕ} {f : Domain n → Ambient q}
    (hf : ContDiff ℝ ∞ f) (x v : Domain n) :
    fderiv ℝ f x v = ∑ i : Fin n, v i • coordinateDerivative f hf i x := by
  have hrepr : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    fderiv ℝ f x v = fderiv ℝ f x (∑ i : Fin n, v i • EuclideanSpace.single i 1) :=
      congrArg (fun w => fderiv ℝ f x w) hrepr.symm
    _ = _ := by simp only [map_sum, map_smul, coordinateDerivative]

private theorem scaled_memLp_ball {n q : ℕ} (a : Domain n) {r R l : ℝ} (hl : 0 < l)
    (hscale : l * r ≤ R) {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    MemLp (fun x => f (a + l • (x - a))) 2 (volume.restrict (Metric.ball a r)) := by
  have hr : r ≤ R / l := (le_div_iff₀ hl).mpr (by simpa only [mul_comm] using hscale)
  exact (memLp_affineBall a a hl R hf).mono_measure
    (Measure.restrict_mono_set volume (Metric.ball_subset_ball hr))

private theorem scaled_eLpNorm_ball_le {n q : ℕ} (a : Domain n) {r R l : ℝ} (hl : 0 < l)
    (hscale : l * r ≤ R) (f : Domain n → Ambient q) :
    eLpNorm (fun x => f (a + l • (x - a))) 2 (volume.restrict (Metric.ball a r)) ≤
      ENNReal.ofReal ((l ^ n)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm f 2 (volume.restrict (Metric.ball a R)) := by
  have hr : r ≤ R / l := (le_div_iff₀ hl).mpr (by simpa only [mul_comm] using hscale)
  exact (eLpNorm_mono_measure _
    (Measure.restrict_mono_set volume (Metric.ball_subset_ball hr))).trans_eq
    (eLpNorm_affineBall a a hl R f)

/-- The actual weak-gradient radial columns control the squared L2 error of
positive dilations on interior concentric balls. -/
theorem memW12_radial_L2_square_le {n q : ℕ} (a : Domain n) {r R l : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hmargin : max 1 l * r < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) :
    (∫ x in Metric.ball a r, ‖u (a + l • (x - a)) - u x‖ ^ 2) ≤
      (l - 1) ^ 2 * (min 1 l)⁻¹ ^ (n + 2) *
        ∫ x in Metric.ball a R, ‖∑ i : Fin n, (x - a) i • Du x i‖ ^ 2 := by
  have hrR : r < R := by
    calc
      r = 1 * r := (one_mul _).symm
      _ ≤ max 1 l * r := mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le
      _ < R := hmargin
  have hscale : l * r ≤ R :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le).trans hmargin.le
  have hR : 0 < R := hr.trans hrR
  obtain ⟨m, hm, hmW, hconv, hDconv⟩ := hu.smoothDensity_memW12_ball hR
  have hmu (k : ℕ) : MemLp (m k) 2 (volume.restrict (Metric.ball a r)) :=
    ((hmW k).2.1).mono_measure (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le))
  have huInner := hu.2.1.mono_measure (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le))
  have hmDiff (k : ℕ) : MemLp (fun x => m k (a + l • (x - a)) - m k x) 2
      (volume.restrict (Metric.ball a r)) :=
    (scaled_memLp_ball a hl hscale (hmW k).2.1).sub (hmu k)
  have huDiff : MemLp (fun x => u (a + l • (x - a)) - u x) 2
      (volume.restrict (Metric.ball a r)) :=
    (scaled_memLp_ball a hl hscale hu.2.1).sub huInner
  let J : ℝ≥0∞ := ENNReal.ofReal ((l ^ n)⁻¹) ^ (1 / 2 : ℝ)
  have hJ : J ≠ ⊤ := by dsimp [J]; finiteness
  have hDiffConv : Tendsto (fun k => eLpNorm
      ((fun x => m k (a + l • (x - a)) - m k x) - (fun x => u (a + l • (x - a)) - u x))
      2 (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := by
    have hupper : Tendsto (fun k => J * eLpNorm (m k - u) 2 (volume.restrict (Metric.ball a R)) +
        eLpNorm (m k - u) 2 (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (ENNReal.Tendsto.const_mul hconv (Or.inr hJ)).add hconv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le)
    intro k
    have heq : ((fun x => m k (a + l • (x - a)) - m k x) - (fun x => u (a + l • (x - a)) - u x)) =
        (fun x => (m k - u) (a + l • (x - a))) - (m k - u) := by
      funext x
      simp only [Pi.sub_apply]
      abel
    dsimp only
    rw [heq]
    exact (eLpNorm_sub_le (scaled_memLp_ball a hl hscale ((hmW k).2.1.sub hu.2.1)).aestronglyMeasurable
      ((hmu k).sub huInner).aestronglyMeasurable (by norm_num)).trans
      (add_le_add (scaled_eLpNorm_ball_le a hl hscale (m k - u))
        (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le))))
  have hleft := HolderToCK.tendsto_integral_norm_sq_of_L2 hmDiff huDiff hDiffConv
  let D : ℕ → Domain n → Gradient n q := fun k x i => coordinateDerivative (m k) (hm k) i x
  have hrawLp (k : ℕ) : MemLp (fun x => ∑ i : Fin n, (x - a) i • D k x i)
      2 (volume.restrict (Metric.ball a R)) := memLp_raw_radial_columns_ball a R (D k) (hmW k).2.2
  have huRawLp : MemLp (fun x => ∑ i : Fin n, (x - a) i • Du x i)
      2 (volume.restrict (Metric.ball a R)) := memLp_raw_radial_columns_ball a R Du hu.2.2
  have hRawConv := tendsto_eLpNorm_raw_radial_columns_sub a R (fun k => (hmW k).2.2) hu.2.2 hDconv
  have henergy := HolderToCK.tendsto_integral_norm_sq_of_L2 hrawLp huRawLp hRawConv
  have henergySmooth : Tendsto (fun k => ∫ x in Metric.ball a R,
      ‖fderiv ℝ (m k) x (x - a)‖ ^ 2) atTop
      (𝓝 (∫ x in Metric.ball a R, ‖∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)) := by
    convert henergy using 1
    funext k
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      congrArg (fun v : Ambient q => ‖v‖ ^ 2) (smooth_fderiv_apply_eq_sum (hm k) x (x - a))
  exact le_of_tendsto_of_tendsto hleft
    (henergySmooth.const_mul ((l - 1) ^ 2 * (min 1 l)⁻¹ ^ (n + 2)))
    (Filter.Eventually.of_forall fun k => smooth_radial_L2_square_le a hr hl hmargin (hm k))

end StratificationTheory
