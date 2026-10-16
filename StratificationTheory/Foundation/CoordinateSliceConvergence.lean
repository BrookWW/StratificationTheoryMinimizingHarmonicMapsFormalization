module

public import StratificationTheory.Foundation.PolarSliceConvergence
public import HarmonicMaps.Analysis.VariableMollificationL2
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A common subsequence for coordinate-slice Sobolev data

Finite families of actual L2 product data admit a single subsequence whose
one-dimensional graph errors converge on a common spatial full-measure set.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace StratificationTheory

/-- Actual L2 data on a product retain L2 membership on almost every fiber. -/
theorem ae_memLp_two_prod_slice {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    {f : α × β → E} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun t => f (x, t)) 2 ν := by
  have hsq := hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hsq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

private theorem tendsto_integral_norm_sq_zero_of_eLpNorm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : ℕ → α → E}
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have heq (k : ℕ) : (∫ x, ‖f k x‖ ^ 2 ∂μ) = (eLpNorm (f k) 2 μ).toReal ^ 2 := by
    have hpos : 0 ≤ ∫ x, ‖f k x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have hnorm : eLpNorm (f k) 2 μ =
        ENNReal.ofReal ((∫ x, ‖f k x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hf k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [hnorm, ENNReal.toReal_ofReal (Real.rpow_nonneg hpos _)]
    exact (Real.rpow_inv_natCast_pow (n := 2) hpos (by decide)).symm
  have ht := ((ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hlim).pow 2
  simpa only [Function.comp_def, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0),
    ← heq] using ht

/-- One strictly increasing subsequence makes every actual L2 product error
converge on the same fiber full-measure set, retaining all original slices. -/
theorem exists_subseq_ae_tendsto_prod_l2_family
    {ι α β E : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}
    [SigmaFinite μ] [SigmaFinite ν]
    {f : ι → ℕ → α × β → E} {u : ι → α × β → E}
    (hf : ∀ i k, MemLp (f i k) 2 (μ.prod ν))
    (hu : ∀ i, MemLp (u i) 2 (μ.prod ν))
    (hlim : ∀ i, Tendsto (fun k => eLpNorm (f i k - u i) 2 (μ.prod ν))
      atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ x ∂μ, ∀ i,
        (∀ k, MemLp (fun t => f i k (x, t)) 2 ν) ∧
        MemLp (fun t => u i (x, t)) 2 ν ∧
        Tendsto (fun k => eLpNorm
          (fun t => f i (κ k) (x, t) - u i (x, t)) 2 ν) atTop (𝓝 0) := by
  classical
  let F : ℕ → α × β → ℝ := fun k p => ∑ i, ‖f i k p - u i p‖ ^ 2
  have heI (i : ι) (k : ℕ) : Integrable (fun p => ‖f i k p - u i p‖ ^ 2) (μ.prod ν) :=
    ((hf i k).sub (hu i)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hF (k : ℕ) : Integrable (F k) (μ.prod ν) :=
    integrable_finsetSum Finset.univ (fun i _ => heI i k)
  have hFn (k : ℕ) (p : α × β) : 0 ≤ F k p :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heLim (i : ι) : Tendsto (fun k => ∫ p, ‖f i k p - u i p‖ ^ 2 ∂μ.prod ν)
      atTop (𝓝 0) :=
    tendsto_integral_norm_sq_zero_of_eLpNorm (fun k => (hf i k).sub (hu i)) (hlim i)
  have hFint (k : ℕ) : (∫ p, F k p ∂μ.prod ν) =
      ∑ i, ∫ p, ‖f i k p - u i p‖ ^ 2 ∂μ.prod ν :=
    integral_finsetSum Finset.univ (fun i _ => heI i k)
  have hFlim : Tendsto (fun k => ∫ p, F k p ∂μ.prod ν) atTop (𝓝 0) := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => heLim i)
    simpa only [← hFint, Finset.sum_const_zero] using ht
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_tendsto_integral_slice_zero
    (μ := ν) (ν := μ) (f := fun k p => F k p.swap)
    (fun k => (hF k).swap) (fun k p => hFn k p.swap)
    (by simpa only [integral_prod_swap] using hFlim)
  have hmaps : ∀ᵐ x ∂μ, ∀ i k, MemLp (fun t => f i k (x, t)) 2 ν :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => ae_memLp_two_prod_slice (hf i k)
  have htargets : ∀ᵐ x ∂μ, ∀ i, MemLp (fun t => u i (x, t)) 2 ν :=
    ae_all_iff.mpr fun i => ae_memLp_two_prod_slice (hu i)
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hκae, hmaps, htargets] with x hx hmx hux
  intro i
  refine ⟨hmx i, hux i, ?_⟩
  have heSlice (k : ℕ) : MemLp (fun t => f i (κ k) (x, t) - u i (x, t)) 2 ν :=
    (hmx i (κ k)).sub (hux i)
  apply tendsto_eLpNorm_two_zero_of_integral_norm_sq heSlice
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx.2
    (fun k => integral_nonneg fun _ => sq_nonneg _)
  intro k
  apply integral_mono (heSlice k |>.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    (hx.1 (κ k))
  intro t
  change ‖f i (κ k) (x, t) - u i (x, t)‖ ^ 2 ≤
    ∑ j, ‖f j (κ k) (x, t) - u j (x, t)‖ ^ 2
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg ‖f j (κ k) (x, t) - u j (x, t)‖) (Finset.mem_univ i)

end StratificationTheory
