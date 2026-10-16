module

public import StratificationTheory.Foundation.PolarSlices
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Subsequence convergence of actual integral slices

Nonnegative L1 errors tending to zero on a product admit one subsequence whose
angular integrals tend to zero almost everywhere. The full-measure set also
retains integrability of every original error slice.
Polar coordinates retain the exact radial Jacobian, and ball-local L2
convergence is applied to the actual squared errors inside the ball.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace StratificationTheory

/-- Vanishing actual nonnegative L1 product errors admit one subsequence with
vanishing angular integrals almost everywhere. Every original angular error
slice is integrable on that same full-measure set. -/
theorem exists_subseq_ae_tendsto_integral_slice_zero
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    {f : ℕ → α × β → ℝ}
    (hf : ∀ k, Integrable (f k) (μ.prod ν))
    (hfn : ∀ k z, 0 ≤ f k z)
    (hlim : Tendsto (fun k => ∫ z, f k z ∂μ.prod ν) atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ y ∂ν,
        (∀ k, Integrable (fun x => f k (x, y)) μ) ∧
        Tendsto (fun k => ∫ x, f (κ k) (x, y) ∂μ) atTop (𝓝 0) := by
  let g : ℕ → β → ℝ := fun k y => ∫ x, f k (x, y) ∂μ
  have hg (k : ℕ) : Integrable (g k) ν := (hf k).integral_prod_right
  have hgn (k : ℕ) (y : β) : 0 ≤ g k y :=
    integral_nonneg fun x => hfn k (x, y)
  have htotal (k : ℕ) : (∫ y, g k y ∂ν) = ∫ z, f k z ∂μ.prod ν :=
    (integral_prod_symm (f k) (hf k)).symm
  have hnorm (k : ℕ) : eLpNorm (g k - (fun _ => (0 : ℝ))) 1 ν =
      ENNReal.ofReal (∫ z, f k z ∂μ.prod ν) := by
    have hsub : g k - (fun _ => (0 : ℝ)) = g k := by
      funext y
      exact sub_zero (g k y)
    rw [hsub]
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hg k)]
    have heq : (∫ y, ‖g k y‖ ∂ν) = ∫ y, g k y ∂ν :=
      integral_congr_ae (Eventually.of_forall fun y => Real.norm_of_nonneg (hgn k y))
    rw [heq, htotal]
  have hLp : Tendsto (fun k => eLpNorm (g k - (fun _ => (0 : ℝ))) 1 ν)
      atTop (𝓝 0) := by
    simp_rw [hnorm]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hm : TendstoInMeasure ν g atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun k => (hg k).aestronglyMeasurable) aestronglyMeasurable_zero hLp
  obtain ⟨κ, hκ, hκlim⟩ := hm.exists_seq_tendsto_ae
  have hslice : ∀ᵐ y ∂ν, ∀ k, Integrable (fun x => f k (x, y)) μ :=
    ae_all_iff.mpr fun k => (hf k).prod_left_ae
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hslice, hκlim] with y hy hyl
  exact ⟨hy, hyl⟩

private theorem integral_polar_product_eq_integral {n : ℕ} (hn : 0 < n)
    (f : Domain n → ℝ) (a : Domain n) :
    (∫ p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ), f (a + p.2.val • p.1.val)
      ∂((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1)))) =
      ∫ x, f x := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫ x : ({(0 : Domain n)}ᶜ : Set (Domain n)), f (a + x.val)
        ∂((volume : Measure (Domain n)).comap (↑)) := by
      have he := hm.integral_comp (Homeomorph.measurableEmbedding _)
        (fun p => f (a + ((homeomorphUnitSphereProd (Domain n)).symm p).val))
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace, Fintype.card_fin] using he.symm
    _ = ∫ x : Domain n, f (a + x) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x : Domain n => f (a + x)), restrict_compl_singleton]
    _ = ∫ x, f x := integral_add_left_eq_self f a

/-- Vanishing nonnegative global L1 errors have one subsequence whose actual
angular integrals vanish at Lebesgue-almost every positive radius, retaining
angular integrability of every original error. -/
theorem exists_subseq_ae_tendsto_polar_integral_zero {n : ℕ} (hn : 0 < n)
    {f : ℕ → Domain n → ℝ} (hf : ∀ k, Integrable (f k) volume)
    (hfn : ∀ k x, 0 ≤ f k x)
    (hlim : Tendsto (fun k => ∫ x, f k x) atTop (𝓝 0)) (a : Domain n) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
        (∀ k, Integrable (fun θ : sphere (0 : Domain n) 1 => f k (a + r • θ.val))
          (volume : Measure (Domain n)).toSphere) ∧
        Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1, f (κ k) (a + r • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
  let F : ℕ → sphere (0 : Domain n) 1 × Ioi (0 : ℝ) → ℝ :=
    fun k p => f k (a + p.2.val • p.1.val)
  have hF (k : ℕ) : Integrable (F k)
      ((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) :=
    integrable_polar_coordinates (hf k) a
  have hFint (k : ℕ) : (∫ p, F k p
      ∂((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1)))) =
      ∫ x, f k x := integral_polar_product_eq_integral hn (f k) a
  have hFlim : Tendsto (fun k => ∫ p, F k p
      ∂((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))))
      atTop (𝓝 0) := by
    simp_rw [hFint]
    exact hlim
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_tendsto_integral_slice_zero hF
    (fun k p => hfn k (a + p.2.val • p.1.val)) hFlim
  refine ⟨κ, hκ, ?_⟩
  apply (ae_restrict_iff_subtype measurableSet_Ioi).mpr
  exact (ae_volumeIoiPow_iff (n - 1)).mp hκae

/-- Vanishing actual nonnegative ball-local L1 errors have one subsequence
whose angular integrals vanish almost everywhere strictly inside the ball.
Every original error retains its actual angular integrability there. -/
theorem exists_subseq_ae_tendsto_polar_integral_zero_ball {n : ℕ} (hn : 0 < n)
    {f : ℕ → Domain n → ℝ} {a : Domain n} {R : ℝ}
    (hf : ∀ k, IntegrableOn (f k) (ball a R)) (hfn : ∀ k x, 0 ≤ f k x)
    (hlim : Tendsto (fun k => ∫ x in ball a R, f k x) atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
        (∀ k, Integrable (fun θ : sphere (0 : Domain n) 1 => f k (a + r • θ.val))
          (volume : Measure (Domain n)).toSphere) ∧
        Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1, f (κ k) (a + r • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
  let g : ℕ → Domain n → ℝ := fun k => (ball a R).indicator (f k)
  have hg (k : ℕ) : Integrable (g k) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (hf k)
  have hgn (k : ℕ) (x : Domain n) : 0 ≤ g k x :=
    indicator_nonneg (fun y _ => hfn k y) x
  have hgint (k : ℕ) : (∫ x, g k x) = ∫ x in ball a R, f k x :=
    integral_indicator measurableSet_ball
  have hglim : Tendsto (fun k => ∫ x, g k x) atTop (𝓝 0) := by
    simp_rw [hgint]
    exact hlim
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_tendsto_polar_integral_zero hn hg hgn hglim a
  have hsub : Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ) := fun _ h => h.1
  have hκinside := hκae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hκinside, ae_restrict_mem measurableSet_Ioo] with r hr hrR
  have heq (k : ℕ) (θ : sphere (0 : Domain n) 1) :
      g k (a + r • θ.val) = f k (a + r • θ.val) := by
    apply indicator_of_mem
    rw [mem_ball, dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hrR.1.le]
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    simpa only [hθ, mul_one] using hrR.2
  simpa only [heq] using hr

private theorem tendsto_integral_norm_sq_zero_of_l2
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

/-- Actual L2 convergence on a ball produces one subsequence with vanishing
actual angular squared errors at almost every interior positive radius.
All original angular squared errors are integrable on the same radial set. -/
theorem exists_subseq_ae_tendsto_polar_l2_ball {n q : ℕ} (hn : 0 < n)
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    {a : Domain n} {R : ℝ}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (ball a R)))
    (hu : MemLp u 2 (volume.restrict (ball a R)))
    (hlim : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict (ball a R)))
      atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
        (∀ k, Integrable (fun θ : sphere (0 : Domain n) 1 =>
          ‖f k (a + r • θ.val) - u (a + r • θ.val)‖ ^ 2)
            (volume : Measure (Domain n)).toSphere) ∧
        Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
          ‖f (κ k) (a + r • θ.val) - u (a + r • θ.val)‖ ^ 2
            ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
  have herr (k : ℕ) : MemLp (f k - u) 2 (volume.restrict (ball a R)) := (hf k).sub hu
  have hint (k : ℕ) : IntegrableOn
      (fun x : Domain n => ‖f k x - u x‖ ^ 2) (ball a R) volume :=
    (herr k).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hsq : Tendsto (fun k => ∫ x in ball a R, ‖f k x - u x‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_norm_sq_zero_of_l2 herr hlim
  exact exists_subseq_ae_tendsto_polar_integral_zero_ball (n := n) hn
    (f := fun k x => ‖f k x - u x‖ ^ 2) hint (fun _ _ => sq_nonneg _) hsq

end StratificationTheory
