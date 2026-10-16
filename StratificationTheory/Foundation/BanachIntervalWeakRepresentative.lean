module

public import StratificationTheory.Foundation.IntervalWeakRepresentative
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Banach-valued interval weak representatives

Actual L2 maps and their distributional derivatives on a bounded interval
have a unique continuous representative on the closed interval. The full
Banach carrier includes complete function spaces used for angular L2 data.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Function
open scoped Topology ENNReal ContDiff
namespace StratificationTheory

private theorem scalar_intervalPrimitive_weakDerivative {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (_hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ x in Ioo a b, deriv φ x * (∫ y in a..x, g y)) =
      -(∫ x in Ioo a b, φ x * g x) := by
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun hx => (lt_irrefl a) (hsφ hx).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun hx => (lt_irrefl b) (hsφ hx).2)
  have hφac := (hφ.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).contDiffOn.absolutelyContinuousOnInterval
    (a := a) (b := b)
  have hGac := hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hparts := hφac.integral_mul_deriv_eq_deriv_mul hGac
  have hderivEq : (∫ x in a..b, φ x * deriv (fun x => ∫ y in a..x, g y) x) =
      ∫ x in a..b, φ x * g x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI) a left_mem_uIcc).deriv]
  rw [hderivEq, hφa, hφb, zero_mul, zero_mul, sub_self, zero_sub] at hparts
  have heq : (∫ x in a..b, deriv φ x * (∫ y in a..x, g y)) =
      -(∫ x in a..b, φ x * g x) := by linarith only [hparts]
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at heq
  exact heq


/-- The actual Banach-valued Bochner primitive has its original L2 weak derivative. -/
theorem banach_intervalPrimitive_weakDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ x in Ioo a b, deriv φ x • (∫ y in a..x, g y)) =
      -(∫ x in Ioo a b, φ x • g x) := by
  have hi := intervalIntegrable_of_memLp_two hab hg
  have hGcont := (intervalPrimitive_absolutelyContinuous hi left_mem_uIcc).continuousOn
  have hGInt : IntegrableOn (fun x => ∫ y in a..x, g y) (Ioo a b) volume := by
    exact (hGcont.intervalIntegrable).1.mono_set Ioo_subset_Ioc_self
  have hφderiv : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hleftInt : IntegrableOn
      (fun x => deriv φ x • (∫ y in a..x, g y)) (Ioo a b) volume :=
    hGInt.smul_of_top_right (hφderiv.memLp_top_of_hasCompactSupport hcφ.deriv _)
  have hrightInt : IntegrableOn (fun x => φ x • g x) (Ioo a b) volume :=
    (hg.integrable (by norm_num)).smul_of_top_right
      (hφ.continuous.memLp_top_of_hasCompactSupport hcφ _)
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  change L (∫ x in Ioo a b, deriv φ x • (∫ y in a..x, g y)) =
    L (-(∫ x in Ioo a b, φ x • g x))
  rw [map_neg, ← L.integral_comp_comm hleftInt, ← L.integral_comp_comm hrightInt]
  simp_rw [L.map_smul, smul_eq_mul]
  have hgi := intervalIntegrable_of_memLp_two hab (hg.continuousLinearMap_comp L)
  have hscalar := scalar_intervalPrimitive_weakDerivative hab hgi hφ hcφ hsφ
  rw [← hscalar]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [L.intervalIntegral_comp_comm
    (hi.mono_set' (by rw [uIoc_of_le hx.1.le, uIoc_of_le hab]; exact Ioc_subset_Ioc_right hx.2.le))]


/-- Actual Banach L2 weak data give an absolutely continuous representative and exact increments. -/
theorem banach_interval_weakDerivative_exists_ac_representative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ}
    (hab : a < b) {f g : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in Ioo a b, deriv φ x • f x) = -(∫ x in Ioo a b, φ x • g x)) :
    ∃ F : ℝ → E, AbsolutelyContinuousOnInterval F a b ∧
      F =ᵐ[volume.restrict (Ioo a b)] f ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F t - F s = ∫ y in s..t, g y := by
  let G : ℝ → E := fun x => ∫ y in a..x, g y
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    intervalPrimitive_absolutelyContinuous (intervalIntegrable_of_memLp_two hab.le hg) left_mem_uIcc
  have hGInt : IntegrableOn G (Ioo a b) volume :=
    hGac.continuousOn.intervalIntegrable.1.mono_set Ioo_subset_Ioc_self
  have hfInt : IntegrableOn f (Ioo a b) volume := hf.integrable (by norm_num)
  have hdInt : IntegrableOn (fun x => f x - G x) (Ioo a b) volume := hfInt.sub hGInt
  have hdWeak : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x in Ioo a b, deriv φ x • (f x - G x)) = 0 := by
    intro φ hφ hcφ hsφ
    have hφD : MemLp (deriv φ) ∞ (volume.restrict (Ioo a b)) :=
      (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hcφ.deriv _
    have hfDInt : IntegrableOn (fun x => deriv φ x • f x) (Ioo a b) volume :=
      hfInt.smul_of_top_right hφD
    have hGDInt : IntegrableOn (fun x => deriv φ x • G x) (Ioo a b) volume :=
      hGInt.smul_of_top_right hφD
    simp_rw [smul_sub]
    rw [integral_sub hfDInt hGDInt,
      hw φ hφ hcφ hsφ, banach_intervalPrimitive_weakDerivative hab.le hg hφ hcφ hsφ, sub_self]
  obtain ⟨c, hc⟩ := interval_ae_eq_const_of_weakDerivative_zero hab hdInt hdWeak
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨fun x => c + G x, hconst.add hGac, ?_, ?_⟩
  · filter_upwards [hc] with x hx
    exact (sub_eq_iff_eq_add.mp hx).symm
  · intro s hs t ht
    rw [add_sub_add_left_eq_sub]
    exact intervalPrimitive_sub hab.le hg hs ht

private theorem banachIntervalRepresentative_norm_sq_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ}
    (hab : a < b) {f g : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (F : C(Icc a b, E))
    (hFae : ∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ = f x)
    (hFbound : ∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤
      |(t : ℝ) - (s : ℝ)| * ∫ x in Ioo a b, ‖g x‖ ^ 2) (t : Icc a b) :
    ‖F t‖ ^ 2 ≤ (2 / (b - a)) * (∫ x in Ioo a b, ‖f x‖ ^ 2) +
      2 * (b - a) * (∫ x in Ioo a b, ‖g x‖ ^ 2) := by
  let μ := volume.restrict (Ioo a b)
  let Eg := ∫ x in Ioo a b, ‖g x‖ ^ 2
  have hEg : 0 ≤ Eg := integral_nonneg (fun x => sq_nonneg ‖g x‖)
  have hpoint : ∀ᵐ x ∂μ, ‖F t‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * (b - a) * Eg := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hFae] with x hx hEq
    let s : Icc a b := ⟨x, hx.1.le, hx.2.le⟩
    have hdist : |(t : ℝ) - x| ≤ b - a := abs_le.mpr
      ⟨by linarith only [t.property.1, hx.2], by linarith only [t.property.2, hx.1]⟩
    have hinc : ‖F t - F s‖ ^ 2 ≤ (b - a) * Eg :=
      (hFbound s t).trans (mul_le_mul_of_nonneg_right hdist hEg)
    have hnorm : ‖F t‖ ≤ ‖F s‖ + ‖F t - F s‖ := by
      calc
        ‖F t‖ = ‖F s + (F t - F s)‖ := by congr 1; abel
        _ ≤ ‖F s‖ + ‖F t - F s‖ := norm_add_le _ _
    have hsquare : ‖F t‖ ^ 2 ≤ 2 * ‖F s‖ ^ 2 + 2 * ‖F t - F s‖ ^ 2 := by
      calc
        ‖F t‖ ^ 2 ≤ (‖F s‖ + ‖F t - F s‖) ^ 2 := by gcongr
        _ ≤ 2 * ‖F s‖ ^ 2 + 2 * ‖F t - F s‖ ^ 2 := by
          nlinarith only [sq_nonneg (‖F s‖ - ‖F t - F s‖)]
    have hs : F s = f x := hEq hx
    rw [hs] at hsquare hinc
    linarith only [hsquare, hinc]
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.integrable_norm_pow (by decide)
  have hmono := integral_mono_ae (integrable_const (‖F t‖ ^ 2))
    (hf2.const_mul 2 |>.add (integrable_const (2 * (b - a) * Eg))) hpoint
  change (∫ x : ℝ, ‖F t‖ ^ 2 ∂μ) ≤
    ∫ x, 2 * ‖f x‖ ^ 2 + 2 * (b - a) * Eg ∂μ at hmono
  have hμ : μ.real univ = b - a := by
    simp only [μ, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  rw [integral_const, integral_add (hf2.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const, smul_eq_mul, smul_eq_mul, hμ] at hmono
  have hlen : 0 < b - a := sub_pos.mpr hab
  calc
    ‖F t‖ ^ 2 ≤ (2 * (∫ x, ‖f x‖ ^ 2 ∂μ) + (b - a) * (2 * (b - a) * Eg)) / (b - a) :=
      (le_div_iff₀ hlen).2 (by linarith only [hmono])
    _ = (2 / (b - a)) * (∫ x in Ioo a b, ‖f x‖ ^ 2) +
        2 * (b - a) * (∫ x in Ioo a b, ‖g x‖ ^ 2) := by
      dsimp [μ, Eg]
      field_simp [hlen.ne']


/-- The same closed-interval continuous representative is unique, with absolute continuity and finite energy bounds. -/
theorem banach_interval_weakDerivative_exists_unique_continuous_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • f x) = -(∫ x, φ x • g x)) :
    ∃! F : C(Icc a b, E),
      (∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ = f x) ∧
      (∃ G : ℝ → E, AbsolutelyContinuousOnInterval G a b ∧
        ∀ x : Icc a b, G x = F x) ∧
      (∀ s t : Icc a b, F t - F s = ∫ y in (s : ℝ)..(t : ℝ), g y) ∧
      (∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤
        |(t : ℝ) - (s : ℝ)| * ∫ y in Ioo a b, ‖g y‖ ^ 2) ∧
      ∀ t : Icc a b, ‖F t‖ ^ 2 ≤ (2 / (b - a)) * (∫ y in Ioo a b, ‖f y‖ ^ 2) +
        2 * (b - a) * (∫ y in Ioo a b, ‖g y‖ ^ 2) := by
  have hwI : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in Ioo a b, deriv φ x • f x) = -(∫ x in Ioo a b, φ x • g x) := by
    intro φ hφ hcφ hsφ
    have hleft : (∫ x in Ioo a b, deriv φ x • f x) = ∫ x, deriv φ x • f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport
        (fun hmem => hx (hsφ (tsupport_deriv_subset hmem))), zero_smul]
    have hright : (∫ x in Ioo a b, φ x • g x) = ∫ x, φ x • g x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsφ hmem)), zero_smul]
    rw [hleft, hright]
    exact hw φ hφ hcφ hsφ
  obtain ⟨G, hGac, hGae, hGinc⟩ :=
    banach_interval_weakDerivative_exists_ac_representative hab hf hg hwI
  have hGcont : ContinuousOn G (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hGac.continuousOn
  let F : C(Icc a b, E) := ⟨fun x => G x, hGcont.restrict⟩
  have hFae : ∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b,
      F ⟨x, hx.1.le, hx.2.le⟩ = f x :=
    (ae_restrict_iff' measurableSet_Ioo).mp hGae
  have hFinc : ∀ s t : Icc a b, F t - F s = ∫ y in (s : ℝ)..(t : ℝ), g y :=
    fun s t => hGinc s s.property t t.property
  have hFbound : ∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤
      |(t : ℝ) - (s : ℝ)| * ∫ y in Ioo a b, ‖g y‖ ^ 2 := by
    intro s t
    rw [hFinc s t]
    exact intervalIntegral_norm_sq_le_total_energy hg s.property t.property
  have hFvalue := banachIntervalRepresentative_norm_sq_bound hab hf F hFae hFbound
  refine ⟨F, ⟨hFae, ⟨G, hGac, fun _ => rfl⟩, hFinc, hFbound, hFvalue⟩, ?_⟩
  intro H hH
  have hMeet : ∀ᵐ x ∂volume.restrict (Ioo a b),
      ∀ hx : x ∈ Ioo a b, H ⟨x, hx.1.le, hx.2.le⟩ = F ⟨x, hx.1.le, hx.2.le⟩ := by
    apply ae_restrict_of_ae
    filter_upwards [hH.1, hFae] with x hx hy hxI
    exact (hx hxI).trans (hy hxI).symm
  have hvol : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨x, hx, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hMeet
  let p : Icc a b := ⟨x, hx.1.le, hx.2.le⟩
  have hp : H p = F p := heq hx
  apply ContinuousMap.ext
  intro t
  have hdiff : H t - H p = F t - F p := (hH.2.2.1 p t).trans (hFinc p t).symm
  rw [hp] at hdiff
  exact sub_left_injective hdiff

end StratificationTheory
