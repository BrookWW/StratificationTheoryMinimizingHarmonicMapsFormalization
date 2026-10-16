module

public import HarmonicMaps.Analysis.MollificationConvolution
public import HarmonicMaps.Analysis.SobolevMollificationGradient
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Group.Integral

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff NNReal

namespace StratificationTheory.Compactness

/-- A fixed smooth compactly supported scalar kernel maps a uniformly
L1-bounded family to a uniformly bounded, uniformly Lipschitz family. -/
theorem convolution_family_uniform_bounds {ι : Type*} {n q : ℕ}
    (kernel : Domain n → ℝ) (hkernel : ContDiff ℝ ∞ kernel)
    (hcompact : HasCompactSupport kernel)
    (F : ι → Domain n → Ambient q) (hF : ∀ i, Integrable (F i) volume)
    (C : ℝ≥0) (hbound : ∀ i, (∫ x, ‖F i x‖) ≤ C) :
    ∃ B L : ℝ≥0,
      (∀ i x, ‖∫ z, kernel (x - z) • F i z‖ ≤ B) ∧
      ∀ i, LipschitzWith L (fun x => ∫ z, kernel (x - z) • F i z) := by
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuous hkernel.continuous
  have hK0 : 0 ≤ K := (norm_nonneg (kernel 0)).trans (hK 0)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hkernel (by simp)
  let K' : ℝ≥0 := ⟨K, hK0⟩
  have hweighted (i : ι) (x : Domain n) : Integrable (fun z => kernel (x - z) • F i z) volume :=
    (hF i).bdd_smul K
      (hkernel.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hK (x - z))
  refine ⟨K' * C, L * C, ?_, ?_⟩
  · intro i x
    calc
      ‖∫ z, kernel (x - z) • F i z‖ ≤ ∫ z, K * ‖F i z‖ := by
        apply norm_integral_le_of_norm_le ((hF i).norm.const_mul K)
        exact Filter.Eventually.of_forall fun z => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)
      _ = K * ∫ z, ‖F i z‖ := integral_const_mul _ _
      _ ≤ K * C := mul_le_mul_of_nonneg_left (hbound i) hK0
      _ = (K' * C : ℝ≥0) := rfl
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hdiff : (fun z => kernel (x - z) • F i z) - (fun z => kernel (y - z) • F i z) =
        fun z => (kernel (x - z) - kernel (y - z)) • F i z := by
      funext z
      simp only [Pi.sub_apply, sub_smul]
    calc
      dist (∫ z, kernel (x - z) • F i z) (∫ z, kernel (y - z) • F i z) =
          ‖∫ z, (kernel (x - z) - kernel (y - z)) • F i z‖ := by
        rw [dist_eq_norm, ← integral_sub (hweighted i x) (hweighted i y)]
        exact congrArg (fun g => ‖∫ z, g z‖) hdiff
      _ ≤ ∫ z, ((L : ℝ) * dist x y) * ‖F i z‖ := by
        apply norm_integral_le_of_norm_le ((hF i).norm.const_mul _)
        exact Filter.Eventually.of_forall fun z => by
          rw [norm_smul, ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_right
            ((hL.dist_le_mul (x - z) (y - z)).trans_eq (by rw [dist_sub_right])) (norm_nonneg _)
      _ = ((L : ℝ) * dist x y) * ∫ z, ‖F i z‖ := integral_const_mul _ _
      _ ≤ ((L : ℝ) * dist x y) * C :=
        mul_le_mul_of_nonneg_left (hbound i) (mul_nonneg L.property dist_nonneg)
      _ = ((L * C : ℝ≥0) : ℝ) * dist x y := by simp only [NNReal.coe_mul]; ring

/-- The actual imported Euclidean mollifications of a uniformly L1-bounded
family share one value bound and one Lipschitz constant at each fixed scale. -/
theorem euclideanMollification_family_uniform_bounds {ι : Type*} {n q : ℕ}
    (Ω : OpenDomain n) (u : ι → Domain n → Ambient q)
    (hu : ∀ i, IntegrableOn (u i) Ω.val volume)
    (C : ℝ≥0) (hbound : ∀ i, (∫ x in Ω.val, ‖u i x‖) ≤ C)
    (h : PositiveRadius) :
    ∃ B L : ℝ≥0,
      (∀ i x, ‖euclideanMollification Ω (u i) (hu i) h x‖ ≤ B) ∧
      ∀ i, LipschitzWith L (euclideanMollification Ω (u i) (hu i) h) := by
  let F : ι → Domain n → Ambient q := fun i => zeroExtensionOn Ω (u i)
  have hFi (i : ι) : Integrable (F i) volume := zeroExtensionOn_integrable Ω (u i) (hu i)
  have hnorm (i : ι) : (∫ x, ‖F i x‖) = ∫ x in Ω.val, ‖u i x‖ := by
    simp only [F, zeroExtensionOn, norm_indicator_eq_indicator_norm, integral_indicator Ω.property.measurableSet]
  have hflip (i : ι) (x : Domain n) : euclideanMollification Ω (u i) (hu i) h x =
      ∫ z, scaledMollifierKernel n h (x - z) • F i z := by
    change (∫ z, scaledMollifierKernel n h z • F i (x - z)) = _
    have heq := (integral_sub_left_eq_self
      (fun z => scaledMollifierKernel n h z • F i (x - z)) x (μ := volume)).symm
    simpa only [sub_sub_cancel] using heq
  obtain ⟨B, L, hB, hL⟩ := convolution_family_uniform_bounds (scaledMollifierKernel n h)
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
    F hFi C (fun i => (hnorm i).symm ▸ hbound i)
  refine ⟨B, L, ?_, ?_⟩
  · intro i x
    rw [hflip]
    exact hB i x
  · intro i
    have heq := funext (hflip i)
    rw [heq]
    exact hL i

end StratificationTheory.Compactness
