module

public import HarmonicMaps.Analysis.SobolevPostcompositionBasic
public import HarmonicMaps.Energy

/-!
# Energy of smooth postcomposition columns

An almost-everywhere operator-norm bound acts on the displayed L2 columns
on the original measure space. Their postcomposition columns are integrable
in squared Hilbert--Schmidt norm with the exact squared operator constant.
-/

public section
open HarmonicMaps MeasureTheory Filter
open scoped ContDiff

namespace StratificationTheory

/-- An actual a.e. derivative bound controls every postcomposition column
and its total finite energy, for any measure and any finite dimensions. -/
theorem smooth_postcomposition_column_energy_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {d q k : ℕ} {v : α → Ambient q} {G : α → Gradient d q}
    (hv : AEStronglyMeasurable v μ) (hG : ∀ i, MemLp (fun x => G x i) 2 μ)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F) (C : NNReal)
    (hDF : ∀ᵐ x ∂μ, ‖fderiv ℝ F (v x)‖ ≤ (C : ℝ)) :
    (∀ i, MemLp (fun x => fderiv ℝ F (v x) (G x i)) 2 μ) ∧
    Integrable (fun x => hsNormSq (fun i => fderiv ℝ F (v x) (G x i))) μ ∧
    (∫ x, hsNormSq (fun i => fderiv ℝ F (v x) (G x i)) ∂μ) ≤
      (C : ℝ) ^ 2 * ∫ x, hsNormSq (G x) ∂μ := by
  have hcol (i : Fin d) : MemLp (fun x => fderiv ℝ F (v x) (G x i)) 2 μ := by
    have hm : AEStronglyMeasurable (fun x => fderiv ℝ F (v x) (G x i)) μ :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (((hF.continuous_fderiv (by simp)).comp_aestronglyMeasurable hv).prodMk
          (hG i).aestronglyMeasurable)
    apply ((hG i).norm.const_mul (C : ℝ)).mono' hm
    filter_upwards [hDF] with x hx
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have henergy : Integrable (fun x => hsNormSq (fun i => fderiv ℝ F (v x) (G x i))) μ :=
    integrable_finsetSum Finset.univ
      (fun i _ => (hcol i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hsource : Integrable (fun x => hsNormSq (G x)) μ :=
    integrable_finsetSum Finset.univ
      (fun i _ => (hG i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hpoint : ∀ᵐ x ∂μ,
      hsNormSq (fun i => fderiv ℝ F (v x) (G x i)) ≤ (C : ℝ) ^ 2 * hsNormSq (G x) := by
    filter_upwards [hDF] with x hx
    simp only [hsNormSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hn := (ContinuousLinearMap.le_opNorm (fderiv ℝ F (v x)) (G x i)).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    calc
      ‖fderiv ℝ F (v x) (G x i)‖ ^ 2 ≤ ((C : ℝ) * ‖G x i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = (C : ℝ) ^ 2 * ‖G x i‖ ^ 2 := mul_pow _ _ _
  refine ⟨hcol, henergy, ?_⟩
  calc
    _ ≤ ∫ x, (C : ℝ) ^ 2 * hsNormSq (G x) ∂μ :=
      integral_mono_ae henergy (hsource.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

end StratificationTheory
