module

public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import StratificationTheory.Foundation.CubicalConeBochner
public import Mathlib.MeasureTheory.Function.L2Space

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original base-time L2 data pull back to the same physical positive cone.
The native norm-square integral has Jacobian t^n and is bounded by the
original product integral times the upper time bound to that power. -/
theorem memLp_two_native_cone_of_product {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {M : ℝ} (hM : 0 ≤ M)
    (hJM : ∀ t ∈ J, t ≤ M) {f : Domain n × ℝ → E}
    (hf : MemLp f 2 ((volume.restrict S).prod (volume.restrict J))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ J ∧ ξ y ∈ S}
    let W : Domain (n + 1) → E := fun y => f (ξ y, T y)
    MemLp W 2 (volume.restrict C) ∧
      (∫ y in C, ‖W y‖ ^ 2) = ∫ t in J, t ^ n * ∫ x in S, ‖f (x, t)‖ ^ 2 ∧
      (∫ y in C, ‖W y‖ ^ 2) ≤
        M ^ n * ∫ p : Domain n × ℝ, ‖f p‖ ^ 2
          ∂((volume.restrict S).prod (volume.restrict J)) := by
  intro e T ξ C W
  let μ := (volume : Measure (Domain n)).restrict S
  let ν := (volume : Measure ℝ).restrict J
  let σ := (volume : Measure (Domain (n + 1))).restrict C
  have hQ := quasiMeasurePreserving_native_inverse_positive_cone hS hJ hJpos
  have hWAS : AEStronglyMeasurable W σ := hf.aestronglyMeasurable.comp_quasiMeasurePreserving hQ
  have hWIprod : Integrable (fun p => ‖f p‖ ^ 2) (μ.prod ν) :=
    hf.integrable_norm_pow (by decide)
  have hProdOfReal : ENNReal.ofReal (∫ p, ‖f p‖ ^ 2 ∂μ.prod ν) =
      ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂μ.prod ν :=
    ofReal_integral_eq_lintegral_ofReal hWIprod (Eventually.of_forall fun _ => sq_nonneg _)
  have hProdFinite : (∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂μ.prod ν) ≠ ⊤ := by
    rw [← hProdOfReal]
    exact ENNReal.ofReal_ne_top
  have hraw (t : ℝ) (ht : 0 < t) (x : Domain n) :
      W (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) = f (x, t) := by
    dsimp only [W, ξ, T]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hJac := lintegral_native_positive_cone hS hJ hJpos
    ((hWAS.norm.pow 2).aemeasurable.ennreal_ofReal)
  change (∫⁻ y, ENNReal.ofReal (‖W y‖ ^ 2) ∂σ) =
    ∫⁻ t, ENNReal.ofReal (t ^ n) * ∫⁻ x,
      ENNReal.ofReal (‖W (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))‖ ^ 2) ∂μ ∂ν at hJac
  have hLInt : (∫⁻ y, ENNReal.ofReal (‖W y‖ ^ 2) ∂σ) =
      ∫⁻ t, ENNReal.ofReal (t ^ n) * ∫⁻ x, ENNReal.ofReal (‖f (x, t)‖ ^ 2) ∂μ ∂ν := by
    rw [hJac]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hJ] with t ht
    simp only [hraw t (hJpos t ht)]
  have hLBound : (∫⁻ y, ENNReal.ofReal (‖W y‖ ^ 2) ∂σ) ≤
      ENNReal.ofReal (M ^ n) * ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂μ.prod ν := by
    rw [hLInt]
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (M ^ n) *
          ∫⁻ x, ENNReal.ofReal (‖f (x, t)‖ ^ 2) ∂μ ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hJ] with t ht
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (hJpos t ht).le (hJM t ht) n)) (by positivity)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact (lintegral_prod_symm (fun p => ENNReal.ofReal (‖f p‖ ^ 2))
          (hf.aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal).symm
  have hWI : Integrable (fun y => ‖W y‖ ^ 2) σ := by
    apply (lintegral_ofReal_ne_top_iff_integrable (hWAS.norm.pow 2)
      (Eventually.of_forall fun _ => sq_nonneg _)).mp
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hProdFinite) hLBound
  refine ⟨(memLp_two_iff_integrable_sq_norm hWAS).mpr hWI, ?_, ?_⟩
  · have h := integral_native_positive_cone hS hJ hJpos hWI
    change (∫ y in C, ‖W y‖ ^ 2) = ∫ t in J, t ^ n * ∫ x in S,
      ‖W (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))‖ ^ 2 at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hJ] with t ht
    simp only [hraw t (hJpos t ht)]
  · have hConeOfReal := ofReal_integral_eq_lintegral_ofReal hWI
      (Eventually.of_forall fun _ => sq_nonneg _)
    rw [← hConeOfReal, ← hProdOfReal, ← ENNReal.ofReal_mul (pow_nonneg hM n)] at hLBound
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hLBound

/-- A genuine original product L2 error tending to zero has a native cone
L2 pullback tending to zero under the same literal inverse coordinates. -/
theorem tendsto_native_cone_L2_of_product {α : Type*} {l : Filter α}
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {M : ℝ} (hM : 0 ≤ M)
    (hJM : ∀ t ∈ J, t ≤ M) {f : α → Domain n × ℝ → E}
    (hf : ∀ᶠ a in l, MemLp (f a) 2 ((volume.restrict S).prod (volume.restrict J)))
    (hlim : Tendsto (fun a => ∫ p : Domain n × ℝ, ‖f a p‖ ^ 2
      ∂((volume.restrict S).prod (volume.restrict J))) l (𝓝 0)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ J ∧ ξ y ∈ S}
    let W : α → Domain (n + 1) → E := fun a y => f a (ξ y, T y)
    (∀ᶠ a in l, MemLp (W a) 2 (volume.restrict C)) ∧
      Tendsto (fun a => ∫ y in C, ‖W a y‖ ^ 2) l (𝓝 0) ∧
      Tendsto (fun a => eLpNorm (W a) 2 (volume.restrict C)) l (𝓝 0) := by
  intro e T ξ C W
  have hdata := hf.mono (fun _ h => memLp_two_native_cone_of_product hS hJ hJpos hM hJM h)
  have hL : ∀ᶠ a in l, MemLp (W a) 2 (volume.restrict C) := hdata.mono fun _ h => h.1
  have hupper : Tendsto (fun a => M ^ n * ∫ p : Domain n × ℝ, ‖f a p‖ ^ 2
      ∂((volume.restrict S).prod (volume.restrict J))) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have hsq : Tendsto (fun a => ∫ y in C, ‖W a y‖ ^ 2) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
      (hdata.mono fun _ h => h.2.2)
  refine ⟨hL, hsq, ?_⟩
  have heq : (fun a => eLpNorm (W a) 2 (volume.restrict C)) =ᶠ[l]
      (fun a => ENNReal.ofReal (Real.sqrt (∫ y in C, ‖W a y‖ ^ 2))) := by
    filter_upwards [hL] with a ha
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using
      ha.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  apply (tendsto_congr' heq).mpr
  have ht := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  simpa only [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero] using ht

end StratificationTheory
