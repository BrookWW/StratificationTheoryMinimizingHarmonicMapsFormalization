module

public import HarmonicMaps.Analysis.SobolevCutoffBoundary
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Ambient interpolation with a genuine smooth cutoff

The literal map `u + χ • (v - u)` has the weak product-rule columns and
graph-norm zero-boundary difference when the cutoff is supported inside the
ball. Its actual HS energy is controlled by the endpoint energies and the L2
discrepancy with the inverse-square transition scale. This is an ambient
construction; neither target-distance control nor annular trace gluing is
asserted.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal BigOperators

namespace StratificationTheory.Interpolation

/-- Compactly supported cutoff interpolation has its literal weak gradient
and genuine zero-boundary difference from the original map. -/
theorem smooth_cutoff_interpolation_graph {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hv : MemW12 (ballDomain a R) v Dv)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Metric.ball a R) :
    MemW12 (ballDomain a R) (fun x => u x + χ x • (v x - u x))
      (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) ∧
    HasZeroBoundaryDifference (ballDomain a R) u Du
      (fun x => u x + χ x • (v x - u x))
      (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) := by
  have hz := (hv.sub hu).smoothCutoff_zeroBoundary_ball hR hχ hcχ hsχ
  have hgraph := hu.sub ((MemW12.zero (ballDomain a R)).sub hz.1)
  have hmap : u - (0 - (fun x => χ x • (v x - u x))) =
      (fun x => u x + χ x • (v x - u x)) := by
    funext x
    change u x - (0 - χ x • (v x - u x)) = _
    simp only [zero_sub, sub_neg_eq_add]
  have hgrad : (fun x i => Du x i - ((0 : Domain n → Gradient n q) x i -
      (coordinateDerivative χ hχ i x • (v x - u x) + χ x • (Dv x i - Du x i)))) =
      (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) := by
    funext x i
    simp only [Pi.zero_apply, zero_sub, sub_neg_eq_add]
  change MemW12 (ballDomain a R) (u - (0 - (fun x => χ x • (v x - u x))))
    (fun x i => Du x i - ((0 : Domain n → Gradient n q) x i -
      (coordinateDerivative χ hχ i x • (v x - u x) + χ x • (Dv x i - Du x i)))) at hgraph
  rw [hmap, hgrad] at hgraph
  refine ⟨hgraph, ?_⟩
  have hdiff : ((fun x => u x + χ x • (v x - u x)) - u) =
      (fun x => χ x • (v x - u x)) := by
    funext x
    simp only [Pi.sub_apply, add_sub_cancel_left]
  have hDdiff : (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
      χ x • (Dv x i - Du x i)) - Du x i) =
      (fun x i => coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i)) := by
    funext x i
    exact add_sub_cancel_left _ _
  change HasZeroBoundaryValues (ballDomain a R)
    ((fun x => u x + χ x • (v x - u x)) - u)
    (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
      χ x • (Dv x i - Du x i)) - Du x i)
  rw [hdiff, hDdiff]
  exact hz

private theorem norm_cutoff_column_sq_le {q : ℕ} (A B d : Ambient q)
    (t s M : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hs : |s| ≤ M) :
    ‖A + (s • d + t • (B - A))‖ ^ 2 ≤
      4 * ‖A‖ ^ 2 + 4 * ‖B‖ ^ 2 + 2 * M ^ 2 * ‖d‖ ^ 2 := by
  have heq : A + (s • d + t • (B - A)) = (1 - t) • A + t • B + s • d := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  have htNorm : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht]; exact ht1
  have hOneNorm : ‖1 - t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)]
    linarith only [ht]
  have hA : ‖(1 - t) • A‖ ≤ ‖A‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right hOneNorm (norm_nonneg A)).trans_eq (one_mul _)
  have hB : ‖t • B‖ ≤ ‖B‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right htNorm (norm_nonneg B)).trans_eq (one_mul _)
  have hleft : ‖(1 - t) • A + t • B‖ ≤ ‖A‖ + ‖B‖ :=
    (norm_add_le _ _).trans (add_le_add hA hB)
  have hright : ‖s • d‖ ≤ M * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg d)
  have hsum : ‖(1 - t) • A + t • B + s • d‖ ≤
      ‖(1 - t) • A + t • B‖ + ‖s • d‖ := norm_add_le _ _
  have hleftSq : ‖(1 - t) • A + t • B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    nlinarith only [hleft, norm_nonneg ((1 - t) • A + t • B),
      norm_nonneg A, norm_nonneg B, sq_nonneg (‖A‖ - ‖B‖)]
  have hrightSq : ‖s • d‖ ^ 2 ≤ M ^ 2 * ‖d‖ ^ 2 := by
    have hnonneg : 0 ≤ M * ‖d‖ := (norm_nonneg (s • d)).trans hright
    nlinarith only [hright, norm_nonneg (s • d), hnonneg]
  have hadd : ‖(1 - t) • A + t • B + s • d‖ ^ 2 ≤
      2 * ‖(1 - t) • A + t • B‖ ^ 2 + 2 * ‖s • d‖ ^ 2 := by
    nlinarith only [hsum, norm_nonneg ((1 - t) • A + t • B + s • d),
      norm_nonneg ((1 - t) • A + t • B), norm_nonneg (s • d),
      sq_nonneg (‖(1 - t) • A + t • B‖ - ‖s • d‖)]
  rw [heq]
  linarith only [hadd, hleftSq, hrightSq]

/-- Actual cutoff interpolation columns have an extended energy estimate
using their genuine scalar derivative bound and the L2 endpoint discrepancy. -/
theorem dirichletEnergy_cutoff_interpolation_le {n q : ℕ} {a : Domain n} {R : ℝ}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hv : MemW12 (ballDomain a R) v Dv)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) {M : ℝ}
    (hvalues : ∀ x ∈ Metric.ball a R, 0 ≤ χ x ∧ χ x ≤ 1)
    (hgrad : ∀ x ∈ Metric.ball a R, ∀ i : Fin n, |coordinateDerivative χ hχ i x| ≤ M) :
    dirichletEnergy (fun x i => Du x i +
      (coordinateDerivative χ hχ i x • (v x - u x) + χ x • (Dv x i - Du x i)))
      (Metric.ball a R) ≤
      4 * dirichletEnergy Du (Metric.ball a R) +
      4 * dirichletEnergy Dv (Metric.ball a R) +
      ENNReal.ofReal (2 * (n : ℝ) * M ^ 2) *
        ∫⁻ x in Metric.ball a R, ENNReal.ofReal (‖v x - u x‖ ^ 2) := by
  have hpoint (x : Domain n) (hx : x ∈ Metric.ball a R) :
      hsNormSq (fun i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) ≤
        4 * hsNormSq (Du x) + 4 * hsNormSq (Dv x) +
          (2 * (n : ℝ) * M ^ 2) * ‖v x - u x‖ ^ 2 := by
    unfold hsNormSq
    calc
      _ ≤ ∑ i : Fin n, (4 * ‖Du x i‖ ^ 2 + 4 * ‖Dv x i‖ ^ 2 +
          2 * M ^ 2 * ‖v x - u x‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => norm_cutoff_column_sq_le _ _ _ _ _ _
          (hvalues x hx).1 (hvalues x hx).2 (hgrad x hx i))
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hC : 0 ≤ 2 * (n : ℝ) * M ^ 2 := by positivity
  have hpointENN : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ENNReal.ofReal (hsNormSq (fun i => Du x i +
        (coordinateDerivative χ hχ i x • (v x - u x) + χ x • (Dv x i - Du x i)))) ≤
      4 * ENNReal.ofReal (hsNormSq (Du x)) +
        4 * ENNReal.ofReal (hsNormSq (Dv x)) +
        ENNReal.ofReal (2 * (n : ℝ) * M ^ 2) * ENNReal.ofReal (‖v x - u x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hp := ENNReal.ofReal_le_ofReal (hpoint x hx)
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) (hsNormSq_nonneg _))
      (mul_nonneg (by norm_num) (hsNormSq_nonneg _))) (mul_nonneg hC (sq_nonneg _)),
      ENNReal.ofReal_add (mul_nonneg (by norm_num) (hsNormSq_nonneg _))
        (mul_nonneg (by norm_num) (hsNormSq_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_mul hC] at hp
    norm_num only [ENNReal.ofReal_ofNat] at hp
    exact hp
  have hU : AEMeasurable (fun x => 4 * ENNReal.ofReal (hsNormSq (Du x)))
      (volume.restrict (Metric.ball a R)) :=
    hu.integrable_hsNormSq.aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul (4 : ℝ≥0∞)
  have hV : AEMeasurable (fun x => 4 * ENNReal.ofReal (hsNormSq (Dv x)))
      (volume.restrict (Metric.ball a R)) :=
    hv.integrable_hsNormSq.aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul (4 : ℝ≥0∞)
  have hsplit := lintegral_add_left' (hU.add hV)
    (fun x => ENNReal.ofReal (2 * (n : ℝ) * M ^ 2) * ENNReal.ofReal (‖v x - u x‖ ^ 2))
  simp only [Pi.add_apply] at hsplit
  unfold dirichletEnergy
  refine (lintegral_mono_ae hpointENN).trans_eq ?_
  rw [hsplit, lintegral_add_left' hU,
    lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- A cutoff with column derivative bound `2 / ε` constructs the actual
ambient competitor with inverse-square discrepancy energy and zero-boundary
difference. Target membership and target-distance estimates remain separate. -/
theorem smooth_cutoff_interpolation_epsilon {n q : ℕ} {a : Domain n} {R ε : ℝ}
    (hR : 0 < R) (_hε : 0 < ε)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hv : MemW12 (ballDomain a R) v Dv)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Metric.ball a R)
    (hvalues : ∀ x ∈ Metric.ball a R, 0 ≤ χ x ∧ χ x ≤ 1)
    (hgrad : ∀ x ∈ Metric.ball a R, ∀ i : Fin n,
      |coordinateDerivative χ hχ i x| ≤ 2 / ε) :
    MemW12 (ballDomain a R) (fun x => u x + χ x • (v x - u x))
      (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) ∧
    HasZeroBoundaryDifference (ballDomain a R) u Du
      (fun x => u x + χ x • (v x - u x))
      (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) ∧
    dirichletEnergy (fun x i => Du x i +
      (coordinateDerivative χ hχ i x • (v x - u x) + χ x • (Dv x i - Du x i)))
      (Metric.ball a R) ≤
      4 * dirichletEnergy Du (Metric.ball a R) +
      4 * dirichletEnergy Dv (Metric.ball a R) +
      ENNReal.ofReal (8 * (n : ℝ) / ε ^ 2) *
        ∫⁻ x in Metric.ball a R, ENNReal.ofReal (‖v x - u x‖ ^ 2) := by
  obtain ⟨hW, hboundary⟩ := smooth_cutoff_interpolation_graph hR hu hv hχ hcχ hsχ
  refine ⟨hW, hboundary, ?_⟩
  have henergy := dirichletEnergy_cutoff_interpolation_le hu hv hχ hvalues hgrad
  have hscale : 2 * (n : ℝ) * (2 / ε) ^ 2 = 8 * (n : ℝ) / ε ^ 2 := by ring
  simpa only [hscale] using henergy

end StratificationTheory.Interpolation

end
