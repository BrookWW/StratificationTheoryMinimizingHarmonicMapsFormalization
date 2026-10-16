module

public import HarmonicMaps.Analysis.SobolevL2Closure
public import HarmonicMaps.Analysis.SmoothWeakGradient
public import HarmonicMaps.Analysis.L2TranslationContinuity

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace StratificationTheory.Interpolation

private theorem eLpNorm_zero_extension_error {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s t : Set (Domain n)} (hs : MeasurableSet s) (hst : s ⊆ t)
    {g f : Domain n → E} (hgs : tsupport g ⊆ s) :
    eLpNorm (g - s.indicator f) 2 (volume.restrict t) =
      eLpNorm (g - f) 2 (volume.restrict s) := by
  classical
  have heq : g - s.indicator f = s.indicator (g - f) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [Pi.sub_apply, indicator_of_mem hx]
    · have hg : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hx (hgs hmem))
      simp only [Pi.sub_apply, indicator_of_notMem hx, hg, sub_zero]
  rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hs, Measure.restrict_restrict hs,
    inter_eq_left.mpr hst]

/-- The zero extension of a genuine zero-boundary graph on an inner ball has
zero-boundary membership on any containing concentric ball, with precisely the
zero-extended original displayed gradient. -/
theorem zeroBoundary_zero_extend_ball {n q : ℕ} {a : Domain n} {r R : ℝ}
    (hrR : r ≤ R) {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : HasZeroBoundaryValues (ballDomain a r) f Df) :
    HasZeroBoundaryValues (ballDomain a R) ((Metric.ball a r).indicator f)
      (fun x i => (Metric.ball a r).indicator (fun y => Df y i) x) := by
  classical
  obtain ⟨hW, m, hm, hmc, hmap, hgrad⟩ := hf
  let F := (Metric.ball a r).indicator f
  let DF : Domain n → Gradient n q := fun x i => (Metric.ball a r).indicator (fun y => Df y i) x
  have hsmall : Metric.ball a r ⊆ Metric.ball a R := Metric.ball_subset_ball hrR
  have hF : MemLp F 2 (volume.restrict (Metric.ball a R)) :=
    (memLp_zeroExtension measurableSet_ball hW.2.1).mono_measure Measure.restrict_le_self
  have hDF (i : Fin n) : MemLp (fun x => DF x i) 2 (volume.restrict (Metric.ball a R)) :=
    (memLp_zeroExtension measurableSet_ball (hW.2.2 i)).mono_measure Measure.restrict_le_self
  have hmW (k : ℕ) : MemW12 (ballDomain a R) (m k)
      (fun x i => coordinateDerivative (m k) (hm k) i x) := by
    apply memW12_of_contDiff (ballDomain a R) (hm k)
    · exact ((hm k).continuous.memLp_of_hasCompactSupport (hmc k).1).mono_measure Measure.restrict_le_self
    · intro i
      have hc : Continuous (coordinateDerivative (m k) (hm k) i) :=
        ((hm k).continuous_fderiv (by simp)).clm_apply (continuous_const (y := EuclideanSpace.single i 1))
      exact (hc.memLp_of_hasCompactSupport ((hmc k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))).mono_measure
        Measure.restrict_le_self
  have hmapR : Tendsto (fun k => eLpNorm (m k - F) 2 (volume.restrict (Metric.ball a R)))
      atTop (𝓝 0) := by
    simpa only [F, eLpNorm_zero_extension_error measurableSet_ball hsmall (hmc _).2, ballDomain] using hmap
  have hgradR (i : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => coordinateDerivative (m k) (hm k) i x - DF x i) 2
      (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
    have hsupport (k : ℕ) : tsupport (coordinateDerivative (m k) (hm k) i) ⊆ Metric.ball a r :=
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hmc k).2
    have heq (k : ℕ) : eLpNorm
        (fun x => coordinateDerivative (m k) (hm k) i x - DF x i) 2
        (volume.restrict (Metric.ball a R)) =
        eLpNorm (fun x => coordinateDerivative (m k) (hm k) i x - Df x i) 2
        (volume.restrict (Metric.ball a r)) := by
      exact eLpNorm_zero_extension_error measurableSet_ball hsmall (hsupport k)
    simpa only [heq, ballDomain] using hgrad i
  refine ⟨MemW12.of_L2_limit_ball a R hmW hF hDF hmapR hgradR, m, hm, ?_, hmapR, hgradR⟩
  intro k
  exact ⟨(hmc k).1, (hmc k).2.trans hsmall⟩

end StratificationTheory.Interpolation
