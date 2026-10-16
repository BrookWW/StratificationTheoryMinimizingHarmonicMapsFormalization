module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# One-dimensional weak derivatives and interval primitives

Weak derivative identities are tested against smooth scalar functions compactly
supported in the open interval. The Bochner primitive of an L2 derivative is
absolutely continuous on the closed interval, has the exact integral increments,
and satisfies the corresponding quadratic energy bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Function
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

private theorem compactTest_antiderivative {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcompact : HasCompactSupport ψ)
    (hsupport : tsupport ψ ⊆ Ioo a b) (hmass : (∫ x, ψ x) = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo a b ∧ deriv φ = ψ := by
  let φ : ℝ → ℝ := fun x => ∫ y in a..x, ψ y
  have hderiv : ∀ x, HasDerivAt φ (ψ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right
      (hψ.continuous.intervalIntegrable a x)
      hψ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuous.continuousAt
  have hd : deriv φ = ψ := funext fun x => (hderiv x).deriv
  have hsmooth : ContDiff ℝ ∞ φ := contDiff_infty_iff_deriv.mpr
    ⟨fun x => (hderiv x).differentiableAt, hd ▸ hψ⟩
  obtain ⟨c, hac, hc⟩ := hcompact.exists_forall_le' continuousOn_id
    (fun x hx => (hsupport hx).1)
  obtain ⟨r, hbr, hr⟩ := hcompact.exists_forall_le' continuousOn_id.neg
    (a := -b) (fun x hx => by
      change -b < -x
      exact neg_lt_neg (hsupport hx).2)
  let d : ℝ := -r
  have hdb : d < b := by dsimp [d]; linarith only [hbr]
  have hdK : ∀ x ∈ tsupport ψ, x ≤ d := by
    intro x hx
    have := hr x hx
    change r ≤ -x at this
    dsimp [d]
    linarith only [this]
  let c' := (a + c) / 2
  let d' := (d + b) / 2
  have hac' : a < c' := by dsimp [c']; linarith only [hac]
  have hc'c : c' < c := by dsimp [c']; linarith only [hac]
  have hdd' : d < d' := by dsimp [d']; linarith only [hdb]
  have hd'b : d' < b := by dsimp [d']; linarith only [hdb]
  have hleft : ∀ x < c', φ x = 0 := by
    intro x hx
    apply intervalIntegral.integral_zero_ae
    filter_upwards with y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hyK
    have hyc := hc y hyK
    change c ≤ y at hyc
    have hymax : y ≤ max a x := hy.2
    have hmax : max a x < c' := max_lt hac' hx
    linarith only [hyc, hymax, hmax, hc'c]
  have hright : ∀ x, d' < x → φ x = 0 := by
    intro x hx
    change (∫ y in a..x, ψ y) = 0
    rw [intervalIntegral.integral_eq_integral_of_support_subset, hmass]
    intro y hy
    have hyK := subset_tsupport ψ hy
    exact ⟨(hsupport hyK).1, (hdK y hyK).trans (hdd'.trans hx).le⟩
  have hsupp : support φ ⊆ Icc c' d' := by
    intro x hx
    exact ⟨le_of_not_gt (fun h => hx (hleft x h)),
      le_of_not_gt (fun h => hx (hright x h))⟩
  have ht : tsupport φ ⊆ Icc c' d' :=
    (closure_mono hsupp).trans isClosed_Icc.closure_subset
  refine ⟨φ, hsmooth, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp,
    ?_, hd⟩
  intro x hx
  exact ⟨hac'.trans_le (ht hx).1, (ht hx).2.trans_lt hd'b⟩

/-- L2 data on a finite open interval are interval integrable, including both
endpoints in the interval-integral convention. -/
theorem intervalIntegrable_of_memLp_two {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  exact hg.integrable (by norm_num)

private theorem integrable_interval_test_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {g : ℝ → E} {φ : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ) :
    IntegrableOn (fun x => φ x • g x) (Ioo a b) volume :=
  (hg.integrable (by norm_num)).smul_of_top_right
    (hφ.continuous.memLp_top_of_hasCompactSupport hcompact _)

private theorem exists_unitMass_interval_test {a b : ℝ} (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo a b ∧ (∫ x, β x) = 1 := by
  let p := (a + b) / 2
  let δ := (b - a) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hab]
  let B : ContDiffBump p := ⟨δ / 2, δ, by linarith only [hδ], by linarith only [hδ]⟩
  refine ⟨B.normed volume, B.contDiff_normed, B.hasCompactSupport_normed, ?_, B.integral_normed⟩
  intro x hx
  rw [B.tsupport_normed_eq] at hx
  change |x - p| ≤ δ at hx
  obtain ⟨hl, hr⟩ := abs_le.mp hx
  dsimp [p, δ] at hl hr
  constructor <;> linarith only [hl, hr, hab]

/-- An integrable vector-valued function whose distributional derivative
vanishes on the open interval is a.e. constant there. -/
theorem interval_ae_eq_const_of_weakDerivative_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {f : ℝ → E}
    (hf : IntegrableOn f (Ioo a b) volume)
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x in Ioo a b, deriv φ x • f x) = 0) :
    ∃ c : E, f =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  obtain ⟨β, hβ, hcβ, hsβ, hmβ⟩ := exists_unitMass_interval_test hab
  let c := ∫ x in Ioo a b, β x • f x
  have hpairInt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
      IntegrableOn (fun x => ψ x • f x) (Ioo a b) volume :=
    hf.smul_of_top_right (hψ.continuous.memLp_top_of_hasCompactSupport hcψ _)
  have hpair : ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x in Ioo a b, ψ x • f x) = (∫ x, ψ x) • c := by
    intro ψ hψ hcψ hsψ
    let M := ∫ x, ψ x
    let ψ₀ : ℝ → ℝ := fun x => ψ x - M • β x
    have hψ₀ : ContDiff ℝ ∞ ψ₀ := hψ.sub (hβ.const_smul M)
    have hcMβ : HasCompactSupport (fun x : ℝ => M • β x) :=
      HasCompactSupport.smul_left (f := fun _ : ℝ => M) hcβ
    have hcψ₀ : HasCompactSupport ψ₀ := hcψ.sub hcMβ
    have hsψ₀ : tsupport ψ₀ ⊆ Ioo a b := by
      apply (tsupport_sub ψ (fun x => M • β x)).trans
      exact union_subset hsψ ((tsupport_smul_subset_right (fun _ => M) β).trans hsβ)
    have hmψ₀ : (∫ x, ψ₀ x) = 0 := by
      change (∫ x, ψ x - M • β x) = 0
      have hMβ : Integrable (fun x => M • β x) volume :=
        (hβ.continuous.integrable_of_hasCompactSupport hcβ).smul M
      rw [integral_sub (hψ.continuous.integrable_of_hasCompactSupport hcψ)
        hMβ, integral_smul,
        hmβ]
      simp only [smul_eq_mul, mul_one, M, sub_self]
    obtain ⟨φ, hφ, hcφ, hsφ, hdφ⟩ := compactTest_antiderivative hψ₀ hcψ₀ hsψ₀ hmψ₀
    have hzero := hw φ hφ hcφ hsφ
    rw [hdφ] at hzero
    change (∫ x in Ioo a b, (ψ x - M • β x) • f x) = 0 at hzero
    simp_rw [sub_smul, smul_eq_mul, mul_smul] at hzero
    have hMβpair : IntegrableOn (fun x => M • (β x • f x)) (Ioo a b) volume :=
      (hpairInt hβ hcβ).smul M
    rw [integral_sub (hpairInt hψ hcψ) hMβpair,
      integral_smul] at hzero
    exact sub_eq_zero.mp hzero
  have hlocal : LocallyIntegrableOn (fun x => f x - c) (Ioo a b) volume :=
    (hf.sub (integrableOn_const (C := c) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))).locallyIntegrableOn
  have hzero : ∀ᵐ x ∂volume, x ∈ Ioo a b → f x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro ψ hψ hcψ hsψ
    have hsIntegral : (∫ x in Ioo a b, ψ x) = ∫ x, ψ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsψ hmem))
    have hzero_on : (∫ x in Ioo a b, ψ x • (f x - c)) = 0 := by
      simp_rw [smul_sub]
      rw [integral_sub (hpairInt hψ hcψ)
        ((hψ.continuous.integrable_of_hasCompactSupport hcψ).integrableOn.smul_const c),
        integral_smul_const, hsIntegral, hpair ψ hψ hcψ hsψ, sub_self]
    have hwhole : (∫ x in Ioo a b, ψ x • (f x - c)) = ∫ x, ψ x • (f x - c) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsψ hmem)), zero_smul]
    exact hwhole.symm.trans hzero_on
  refine ⟨c, (ae_restrict_iff' measurableSet_Ioo).2 ?_⟩
  filter_upwards [hzero] with x hx hxI
  exact sub_eq_zero.mp (hx hxI)

/-- Actual Bochner weak derivatives of one fixed map are unique a.e. on the
open interval. The inputs are L2 data and the distributional test identities. -/
theorem interval_weakDerivative_unique {q : ℕ} {a b : ℝ}
    {f g h : ℝ → Ambient q}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hfg : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in Ioo a b, deriv φ x • f x) = -(∫ x in Ioo a b, φ x • g x))
    (hfh : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in Ioo a b, deriv φ x • f x) = -(∫ x in Ioo a b, φ x • h x)) :
    g =ᵐ[volume.restrict (Ioo a b)] h := by
  have hi : IntegrableOn (fun x => g x - h x) (Ioo a b) volume :=
    (hg.integrable (by norm_num)).sub (hh.integrable (by norm_num))
  have hlocal := hi.locallyIntegrableOn
  have hzero : ∀ᵐ x ∂volume, x ∈ Ioo a b → g x - h x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro φ hφ hcompact hsupport
    have hpair : (∫ x in Ioo a b, φ x • g x) = ∫ x in Ioo a b, φ x • h x := by
      apply neg_injective
      exact (hfg φ hφ hcompact hsupport).symm.trans (hfh φ hφ hcompact hsupport)
    have hzero_on : (∫ x in Ioo a b, φ x • (g x - h x)) = 0 := by
      simp_rw [smul_sub]
      rw [integral_sub (integrable_interval_test_smul hg hφ hcompact)
        (integrable_interval_test_smul hh hφ hcompact), hpair, sub_self]
    have hwhole : (∫ x in Ioo a b, φ x • (g x - h x)) =
        ∫ x, φ x • (g x - h x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hnot : x ∉ tsupport φ := fun hmem => hx (hsupport hmem)
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]
    exact hwhole.symm.trans hzero_on
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hzero] with x hx hxI
  exact sub_eq_zero.mp (hx hxI)

/-- The Banach-valued interval primitive is absolutely continuous. -/
theorem intervalPrimitive_absolutelyContinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b c : ℝ} {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ y in c..x, g y) a b := by
  let s := fun J : ℕ × (ℕ → ℝ × ℝ) =>
    ⋃ i ∈ Finset.range J.1, uIoc (J.2 i).1 (J.2 i).2
  have hlim : Tendsto
      (fun J => ∫⁻ x in s J, ‖g x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero (ne_of_lt hg.def'.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        a b)
  have hreal := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  apply squeeze_zero' ?_ ?_ hreal
  · filter_upwards with J
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  simp only [comp_apply, s]
  have hwithin : ∀ᶠ J : ℕ × (ℕ → ℝ × ℝ) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      J ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hwithin] with J hJ
  obtain ⟨hends, hdisj⟩ := mem_setOf_eq ▸ hJ
  rw [← integral_norm_eq_lintegral_enorm (hg.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hdisj]
  · apply Finset.sum_le_sum
    intro i hi
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
      (hg.mono_set' (by grind [uIoc, uIcc]))
      (hg.mono_set' (by grind [uIoc, uIcc])),
      Measure.restrict_restrict_of_subset
        (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hJ
          (Finset.mem_range.mp hi))]
    simpa only [uIoc_comm] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc
        (f := g) (a := (J.2 i).2) (b := (J.2 i).1) (μ := volume))
  · intro i hi
    unfold IntegrableOn
    rw [Measure.restrict_restrict_of_subset
      (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hJ
        (Finset.mem_range.mp hi))]
    exact IntegrableOn.mono_set hg.def'.norm
      (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hJ
        (Finset.mem_range.mp hi))

/-- L2 derivative data produce an absolutely continuous Bochner primitive
on the actual closed interval. -/
theorem intervalPrimitive_absolutelyContinuous_of_memLp_two {q : ℕ} {a b : ℝ}
    (hab : a ≤ b) {g : ℝ → Ambient q}
    (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    AbsolutelyContinuousOnInterval (fun x => ∫ y in a..x, g y) a b :=
  intervalPrimitive_absolutelyContinuous (intervalIntegrable_of_memLp_two hab hg)
    left_mem_uIcc

/-- The primitive has the exact oriented integral increment between any two
points of the interval, in either order. -/
theorem intervalPrimitive_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b s t : ℝ} (hab : a ≤ b) {g : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ y in a..t, g y) - (∫ y in a..s, g y) = ∫ y in s..t, g y := by
  have hi := intervalIntegrable_of_memLp_two hab hg
  exact intervalIntegral.integral_interval_sub_left
    (hi.mono_set' (by rw [uIoc_of_le ht.1, uIoc_of_le hab]; exact Ioc_subset_Ioc_right ht.2))
    (hi.mono_set' (by rw [uIoc_of_le hs.1, uIoc_of_le hab]; exact Ioc_subset_Ioc_right hs.2))

private theorem integral_norm_sq_eq_norm_toLp_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {g : α → E} (hg : MemLp g 2 μ) :
    (∫ x, ‖g x‖ ^ 2 ∂μ) = ‖hg.toLp g‖ ^ 2 := by
  calc
    (∫ x, ‖g x‖ ^ 2 ∂μ) =
        ∫ x, inner ℝ ((hg.toLp g) x) ((hg.toLp g) x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = inner ℝ (hg.toLp g) (hg.toLp g) := (L2.inner_def _ _).symm
    _ = ‖hg.toLp g‖ ^ 2 := real_inner_self_eq_norm_sq _

private theorem norm_integral_sq_le_measure_mul_integral_norm_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → E} (hg : MemLp g 2 μ) :
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ μ.real univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have hn := hg.norm
  have h1 : MemLp (fun _ : α => (1 : ℝ)) 2 μ := memLp_const 1
  let A := hn.toLp (fun x => ‖g x‖)
  let B := h1.toLp (fun _ : α => (1 : ℝ))
  have hAB : inner ℝ A B = ∫ x, ‖g x‖ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hn.coeFn_toLp, h1.coeFn_toLp] with x hx hy
    change inner ℝ ((hn.toLp (fun x => ‖g x‖)) x) ((h1.toLp (fun _ => 1)) x) = ‖g x‖
    rw [hx, hy]
    change 1 * ‖g x‖ = ‖g x‖
    exact one_mul _
  have hA : ‖A‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    rw [← integral_norm_sq_eq_norm_toLp_sq hn]
    simp only [Real.norm_eq_abs, abs_norm]
  have hB : ‖B‖ ^ 2 = μ.real univ := by
    rw [← integral_norm_sq_eq_norm_toLp_sq h1]
    simp only [norm_one, one_pow, integral_const, smul_eq_mul, mul_one]
  have hi0 : 0 ≤ ∫ x, ‖g x‖ ∂μ := integral_nonneg (fun x => norm_nonneg (g x))
  calc
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ (∫ x, ‖g x‖ ∂μ) ^ 2 := by
      gcongr
      exact norm_integral_le_integral_norm g
    _ = ‖inner ℝ A B‖ ^ 2 := by rw [hAB, Real.norm_of_nonneg hi0]
    _ ≤ (‖A‖ * ‖B‖) ^ 2 := by gcongr; exact norm_inner_le_norm A B
    _ = ‖A‖ ^ 2 * ‖B‖ ^ 2 := mul_pow _ _ _
    _ = μ.real univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by rw [hA, hB, mul_comm]

/-- The square of the Bochner integral is bounded by interval length times
the actual quadratic energy of its L2 integrand. -/
theorem intervalIntegral_norm_sq_le_of_memLp_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    ‖∫ x in a..b, g x‖ ^ 2 ≤ (b - a) * ∫ x in Ioo a b, ‖g x‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  have h := norm_integral_sq_le_measure_mul_integral_norm_sq hg
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

/-- Every increment is bounded by its length times the total quadratic
energy on the source interval. Both orders and coincident points are covered. -/
theorem intervalIntegral_norm_sq_le_total_energy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b s t : ℝ}
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖∫ x in s..t, g x‖ ^ 2 ≤ |t - s| * ∫ x in Ioo a b, ‖g x‖ ^ 2 := by
  have hsub : Ioo (min s t) (max s t) ⊆ Ioo a b := by
    intro x hx
    exact ⟨(le_min hs.1 ht.1).trans_lt hx.1, hx.2.trans_le (max_le hs.2 ht.2)⟩
  have hgsub := hg.mono_measure (Measure.restrict_mono_set volume hsub)
  have henergy : (∫ x in Ioo (min s t) (max s t), ‖g x‖ ^ 2) ≤
      ∫ x in Ioo a b, ‖g x‖ ^ 2 :=
    setIntegral_mono_set (hg.integrable_norm_pow (by decide))
      (Eventually.of_forall (fun x => sq_nonneg ‖g x‖))
      (Eventually.of_forall (fun _ hx => hsub hx))
  rw [← intervalIntegral.norm_integral_min_max g]
  calc
    ‖∫ x in min s t..max s t, g x‖ ^ 2 ≤
        (max s t - min s t) * ∫ x in Ioo (min s t) (max s t), ‖g x‖ ^ 2 :=
      intervalIntegral_norm_sq_le_of_memLp_two min_le_max hgsub
    _ ≤ (max s t - min s t) * ∫ x in Ioo a b, ‖g x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr min_le_max)
    _ = |t - s| * ∫ x in Ioo a b, ‖g x‖ ^ 2 := by
      rw [max_sub_min_eq_abs', abs_sub_comm s t]

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

/-- The actual Bochner primitive satisfies the distributional identity with
the supplied L2 function as its weak derivative. -/
theorem intervalPrimitive_weakDerivative {q : ℕ} {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → Ambient q} (hg : MemLp g 2 (volume.restrict (Ioo a b)))
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
  have hrightInt := integrable_interval_test_smul hg hφ hcφ
  ext i
  let L : Ambient q →L[ℝ] ℝ := EuclideanSpace.proj i
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

/-- L2 maps with the genuine weak derivative identity admit an absolutely
continuous interval representative with the exact integral increments. -/
theorem interval_weakDerivative_exists_ac_representative {q : ℕ} {a b : ℝ}
    (hab : a < b) {f g : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in Ioo a b, deriv φ x • f x) = -(∫ x in Ioo a b, φ x • g x)) :
    ∃ F : ℝ → Ambient q, AbsolutelyContinuousOnInterval F a b ∧
      F =ᵐ[volume.restrict (Ioo a b)] f ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F t - F s = ∫ y in s..t, g y := by
  let G : ℝ → Ambient q := fun x => ∫ y in a..x, g y
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    intervalPrimitive_absolutelyContinuous_of_memLp_two hab.le hg
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
      hw φ hφ hcφ hsφ, intervalPrimitive_weakDerivative hab.le hg hφ hcφ hsφ, sub_self]
  obtain ⟨c, hc⟩ := interval_ae_eq_const_of_weakDerivative_zero hab hdInt hdWeak
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨fun x => c + G x, hconst.add hGac, ?_, ?_⟩
  · filter_upwards [hc] with x hx
    exact (sub_eq_iff_eq_add.mp hx).symm
  · intro s hs t ht
    rw [add_sub_add_left_eq_sub]
    exact intervalPrimitive_sub hab.le hg hs ht

private theorem intervalRepresentative_norm_sq_bound {q : ℕ} {a b : ℝ}
    (hab : a < b) {f g : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (F : C(Icc a b, Ambient q))
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

/-- The interval representative is unique on its actual closed-interval
carrier. Absolute continuity is witnessed by an extension agreeing there. -/
theorem interval_weakDerivative_exists_unique_continuous_representative
    {q : ℕ} {a b : ℝ} (hab : a < b) {f g : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • f x) = -(∫ x, φ x • g x)) :
    ∃! F : C(Icc a b, Ambient q),
      (∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ = f x) ∧
      (∃ G : ℝ → Ambient q, AbsolutelyContinuousOnInterval G a b ∧
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
    interval_weakDerivative_exists_ac_representative hab hf hg hwI
  have hGcont : ContinuousOn G (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hGac.continuousOn
  let F : C(Icc a b, Ambient q) := ⟨fun x => G x, hGcont.restrict⟩
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
  have hFvalue := intervalRepresentative_norm_sq_bound hab hf F hFae hFbound
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
