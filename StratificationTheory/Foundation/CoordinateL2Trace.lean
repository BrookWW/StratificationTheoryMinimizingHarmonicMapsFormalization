module

public import StratificationTheory.Foundation.IntervalClosedConstraints
public import HarmonicMaps.Analysis.VariableMollificationL2
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Continuous L2 traces for finite spatial measures

Actual finite-product L2 data lift to Bochner L2 curves. Their original
fiberwise distributional time identity determines a unique continuous
closed-interval L2 representative with the original interior slice classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter MeasurableSpace
open scoped Topology ENNReal ContDiff
namespace StratificationTheory

private theorem measurable_of_all_dist {α β : Type*} [MeasurableSpace α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    {F : α → β} (hF : ∀ c : β, Measurable (fun t => dist (F t) c)) : Measurable F := by
  classical
  apply measurable_of_isOpen
  intro U hU
  have hr (x : U) : ∃ r : ℝ, 0 < r ∧ ball x.val r ⊆ U :=
    isOpen_iff.mp hU x.val x.property
  choose r hr hsub using hr
  have hcover : (⋃ x : U, ball x.val (r x)) = U := by
    apply Subset.antisymm (iUnion_subset fun x => hsub x)
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨T, hT, hUnion⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball x.val (r x)) (fun _ => isOpen_ball)
  rw [← hcover, ← hUnion]
  simp only [preimage_iUnion]
  exact MeasurableSet.biUnion hT (fun x _ => measurableSet_lt (hF x.val) measurable_const)

private theorem stronglyMeasurable_curried_lp_two {α : Type*} [MeasurableSpace α] {q : ℕ}
    (σ : Measure α) [IsFiniteMeasure σ] [IsSeparable σ]
    {g : α × ℝ → Ambient q} (hg : StronglyMeasurable g) :
    ∃ F : ℝ → Lp (Ambient q) 2 σ, StronglyMeasurable F ∧
      ∀ t (ht : MemLp (fun θ => g (θ, t)) 2 σ), F t = ht.toLp (fun θ => g (θ, t)) := by
  classical
  let F : ℝ → Lp (Ambient q) 2 σ := fun t =>
    if ht : MemLp (fun θ => g (θ, t)) 2 σ then ht.toLp (fun θ => g (θ, t)) else 0
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp (Ambient q) 2 σ) := borel (Lp (Ambient q) 2 σ)
  letI : BorelSpace (Lp (Ambient q) 2 σ) := ⟨rfl⟩
  have hcur : StronglyMeasurable (Function.uncurry (fun t θ => g (θ, t))) :=
    hg.comp_measurable measurable_swap
  have hgood : MeasurableSet {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ} := by
    have hsq : StronglyMeasurable (Function.uncurry (fun t θ => ‖g (θ, t)‖ ^ 2)) :=
      hcur.norm.pow 2
    have hi := measurableSet_integrable (μ := σ) hsq
    convert hi using 1
    ext t
    exact memLp_two_iff_integrable_sq_norm (hcur.of_uncurry_left.aestronglyMeasurable)
  refine ⟨F, ?_, ?_⟩
  ·
    apply Measurable.stronglyMeasurable
    apply measurable_of_all_dist
    intro c
    have hdiff : StronglyMeasurable (Function.uncurry (fun t θ => ‖g (θ, t) - c θ‖ ^ 2)) := by
      exact (hcur.sub (Lp.stronglyMeasurable c |>.comp_measurable measurable_snd)).norm.pow 2
    have hInt : StronglyMeasurable (fun t : ℝ => ∫ θ, ‖g (θ, t) - c θ‖ ^ 2 ∂σ) :=
      hdiff.integral_prod_right
    have hEq : (fun t : ℝ => dist (F t) c) =
        {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ}.piecewise
          (fun t => Real.sqrt (∫ θ, ‖g (θ, t) - c θ‖ ^ 2 ∂σ)) (fun _ => dist 0 c) := by
      funext t
      by_cases ht : MemLp (fun θ => g (θ, t)) 2 σ
      · rw [Set.piecewise_eq_of_mem {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ} _ _ ht]
        simp only [F, dif_pos ht]
        have hc : (Lp.memLp c).toLp (fun θ => c θ) = c := Lp.toLp_coeFn c (Lp.memLp c)
        have hnorm : ‖ht.toLp (fun θ => g (θ, t)) - c‖ ^ 2 =
            ∫ θ, ‖g (θ, t) - c θ‖ ^ 2 ∂σ := by
          rw [← hc, ← ht.toLp_sub (Lp.memLp c), Lp.norm_toLp,
            ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (ht.sub (Lp.memLp c))]
          simp only [hc, Pi.sub_apply]
        rw [dist_eq_norm, ← hnorm, Real.sqrt_sq (norm_nonneg _)]
      · rw [Set.piecewise_eq_of_notMem {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ} _ _ ht]
        simp only [F, dif_neg ht]
    rw [hEq]
    exact Measurable.piecewise hgood (Real.continuous_sqrt.measurable.comp hInt.measurable) measurable_const
  · intro t ht
    simp only [F, dif_pos ht]


/-- Actual finite product L2 data provide a strongly measurable
L2-valued time curve representing their actual slices, with the exact energy. -/
theorem exists_finite_lp_two_time_curve {α : Type*} [MeasurableSpace α] {q : ℕ}
    (σ : Measure α) [IsFiniteMeasure σ] [IsSeparable σ] (a b : ℝ)
    {f : α × ℝ → Ambient q}
    (hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b)))) :
    ∃ F : ℝ → Lp (Ambient q) 2 σ,
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t))) ∧
      (∫ t in Icc a b, ‖F t‖ ^ 2) =
        ∫ p : α × ℝ, ‖f p‖ ^ 2
          ∂(σ.prod
            (volume.restrict (Icc a b))) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let μ := σ.prod ν
  let g : α × ℝ → Ambient q := hf.aestronglyMeasurable.mk f
  have hgS : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 μ := hf.ae_eq hfg
  obtain ⟨F, hFS, hFslice⟩ := stronglyMeasurable_curried_lp_two σ hgS
  have hgSlice : ∀ᵐ t ∂ν, MemLp (fun θ => g (θ, t)) 2 σ := by
    have hsq := hg.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    filter_upwards [hg.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with t hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have hfgSlice : ∀ᵐ t ∂ν, (fun θ => f (θ, t)) =ᵐ[σ] (fun θ => g (θ, t)) := by
    have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hfg
    exact Measure.ae_ae_of_ae_prod hswap
  have hFslices : ∀ᵐ t ∂ν, ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ,
      F t = ht.toLp (fun θ => f (θ, t)) := by
    filter_upwards [hgSlice, hfgSlice] with t hgt hft
    have ht := hgt.ae_eq hft.symm
    exact ⟨ht, (hFslice t hgt).trans (hgt.toLp_congr ht hft.symm)⟩
  have hnorm : ∀ᵐ t ∂ν, ‖F t‖ ^ 2 = ∫ θ, ‖f (θ, t)‖ ^ 2 ∂σ := by
    filter_upwards [hFslices] with t ht
    obtain ⟨hft, hFt⟩ := ht
    rw [hFt, Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq hft]
  have hsq : Integrable (fun p => ‖f p‖ ^ 2) μ :=
    hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hFInt : Integrable (fun t => ‖F t‖ ^ 2) ν :=
    hsq.integral_prod_right.congr (Filter.EventuallyEq.symm hnorm)
  have hFL : MemLp F 2 ν := (memLp_two_iff_integrable_sq_norm hFS.aestronglyMeasurable).mpr hFInt
  exact ⟨F, hFL, hFslices, (integral_congr_ae hnorm).trans (integral_prod_symm _ hsq).symm⟩


/-- The Bochner integral of the actual slice curve has the original product
pairings against every spatial L2 class. -/
theorem exists_finite_lp_two_time_curve_with_pairings {α : Type*} [MeasurableSpace α] {q : ℕ}
    (σ : Measure α) [IsFiniteMeasure σ] [IsSeparable σ] (a b : ℝ)
    {f : α × ℝ → Ambient q}
    (hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b)))) :
    ∃ F : ℝ → Lp (Ambient q) 2 σ,
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t))) ∧
      ∀ (φ : ℝ → ℝ), Continuous φ → HasCompactSupport φ →
        ∀ c : Lp (Ambient q) 2 σ,
          inner ℝ c (∫ t in Icc a b, φ t • F t) =
            ∫ θ, (∫ t in Icc a b, φ t * inner ℝ (c θ) (f (θ, t))) ∂σ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  obtain ⟨F, hF, hFs, _⟩ := exists_finite_lp_two_time_curve σ a b hf
  refine ⟨F, hF, hFs, ?_⟩
  intro φ hφ hφc c
  have hφL : MemLp φ ∞ ν := hφ.memLp_top_of_hasCompactSupport hφc ν
  have hφP : MemLp (fun p : α × ℝ => φ p.2) ∞ (σ.prod ν) :=
    hφL.comp_snd σ
  have hweighted : MemLp (fun p => φ p.2 • f p) 2 (σ.prod ν) := hf.smul hφP
  have hcP : MemLp (fun p : α × ℝ => c p.1) 2 (σ.prod ν) :=
    (Lp.memLp c).comp_fst ν
  have hpI : Integrable (fun p : α × ℝ =>
      inner ℝ (c p.1) (φ p.2 • f p)) (σ.prod ν) := by
    have hi := L2.integrable_inner (𝕜 := ℝ) (hcP.toLp _) (hweighted.toLp _)
    apply hi.congr
    filter_upwards [hcP.coeFn_toLp, hweighted.coeFn_toLp] with p hc hf
    rw [hc, hf]
  have hFW : MemLp (fun t => φ t • F t) 2 ν := hF.smul hφL
  have hFI : Integrable (fun t => φ t • F t) ν := hFW.integrable (by norm_num)
  rw [← integral_inner hFI c]
  have hpair : ∀ᵐ t ∂ν, inner ℝ c (φ t • F t) =
      ∫ θ, inner ℝ (c θ) (φ t • f (θ, t)) ∂σ := by
    filter_upwards [hFs] with t ht
    obtain ⟨hft, hFt⟩ := ht
    have hinner : inner ℝ c (hft.toLp (fun θ => f (θ, t))) =
        ∫ θ, inner ℝ (c θ) (f (θ, t)) ∂σ := by
      rw [L2.inner_def]
      exact integral_congr_ae (hft.coeFn_toLp.mono fun θ hθ => by exact congrArg (inner ℝ (c θ)) hθ)
    rw [hFt, inner_smul_right, hinner]
    simp only [inner_smul_right]
    exact (integral_const_mul (φ t) _).symm
  rw [integral_congr_ae hpair, ← integral_prod_symm _ hpI, integral_prod _ hpI]
  simp only [inner_smul_right]
  rfl

/-- Actual finite product L2 data with their per-angle vector weak derivative
admit the same L2-valued slice representatives and their Bochner weak identity. -/
theorem exists_finite_lp_two_time_curves_with_weak_identity
    {α : Type*} [MeasurableSpace α] {q : ℕ}
    (σ : Measure α) [IsFiniteMeasure σ] [IsSeparable σ] (a b : ℝ)
    {f g : α × ℝ → Ambient q}
    (hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b))))
    (hg : MemLp g 2 (σ.prod (volume.restrict (Icc a b))))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ θ ∂σ,
        (∫ t in Icc a b, deriv φ t • f (θ, t)) =
          -(∫ t in Icc a b, φ t • g (θ, t))) :
    ∃ F G : ℝ → Lp (Ambient q) 2 σ,
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      MemLp G 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t))) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => g (θ, t)) 2 σ, G t = ht.toLp (fun θ => g (θ, t))) ∧
      ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b →
        Integrable (fun t => deriv φ t • F t) ∧
        Integrable (fun t => φ t • G t) ∧
        (∫ t, deriv φ t • F t) = -(∫ t, φ t • G t) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  obtain ⟨F, hF, hFs, hFp⟩ := exists_finite_lp_two_time_curve_with_pairings σ a b hf
  obtain ⟨G, hG, hGs, hGp⟩ := exists_finite_lp_two_time_curve_with_pairings σ a b hg
  refine ⟨F, G, hF, hG, hFs, hGs, ?_⟩
  intro φ hφ hcφ hsφ
  have hD : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hDL : MemLp (deriv φ) ∞ ν := hD.memLp_top_of_hasCompactSupport hcφ.deriv ν
  have hφL : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hcφ ν
  have hDFL : MemLp (fun t => deriv φ t • F t) 2 ν := hF.smul hDL
  have hφGL : MemLp (fun t => φ t • G t) 2 ν := hG.smul hφL
  have hDF : Integrable (fun t => deriv φ t • F t) ν := hDFL.integrable (by norm_num)
  have hφG : Integrable (fun t => φ t • G t) ν := hφGL.integrable (by norm_num)
  have hDFsupp : Function.support (fun t => deriv φ t • F t) ⊆ Icc a b := by
    intro t ht
    have hDt : deriv φ t ≠ 0 := by
      intro hz
      apply ht
      change deriv φ t • F t = 0
      rw [hz, zero_smul]
    exact Ioo_subset_Icc_self (hsφ (tsupport_deriv_subset (subset_tsupport _ hDt)))
  have hφGsupp : Function.support (fun t => φ t • G t) ⊆ Icc a b := by
    intro t ht
    have hφt : φ t ≠ 0 := by
      intro hz
      apply ht
      change φ t • G t = 0
      rw [hz, zero_smul]
    exact Ioo_subset_Icc_self (hsφ (subset_tsupport _ hφt))
  refine ⟨(integrableOn_iff_integrable_of_support_subset hDFsupp).mp hDF,
    (integrableOn_iff_integrable_of_support_subset hφGsupp).mp hφG, ?_⟩
  have hleft : (∫ t in Icc a b, deriv φ t • F t) = ∫ t, deriv φ t • F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun hmem => ht (hDFsupp hmem))
  have hright : (∫ t in Icc a b, φ t • G t) = ∫ t, φ t • G t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun hmem => ht (hφGsupp hmem))
  rw [← hleft, ← hright]
  apply ext_inner_left ℝ
  intro c
  rw [inner_neg_right, hFp (deriv φ) hD hcφ.deriv c, hGp φ hφ.continuous hcφ c,
    ← integral_neg]
  have hDProd : MemLp (fun p : α × ℝ => deriv φ p.2) ∞ (σ.prod ν) :=
    hDL.comp_snd σ
  have hφProd : MemLp (fun p : α × ℝ => φ p.2) ∞ (σ.prod ν) :=
    hφL.comp_snd σ
  have hDfL : MemLp (fun p => deriv φ p.2 • f p) 2 (σ.prod ν) := hf.smul hDProd
  have hφgL : MemLp (fun p => φ p.2 • g p) 2 (σ.prod ν) := hg.smul hφProd
  have hDf : Integrable (fun p => deriv φ p.2 • f p) (σ.prod ν) := hDfL.integrable (by norm_num)
  have hφg : Integrable (fun p => φ p.2 • g p) (σ.prod ν) := hφgL.integrable (by norm_num)
  apply integral_congr_ae
  filter_upwards [hDf.prod_right_ae, hφg.prod_right_ae, hw φ hφ hcφ hsφ] with θ hfθ hgθ hwθ
  calc
    (∫ t in Icc a b, deriv φ t * inner ℝ (c θ) (f (θ, t))) =
        inner ℝ (c θ) (∫ t in Icc a b, deriv φ t • f (θ, t)) := by
      simpa only [inner_smul_right] using (integral_inner (𝕜 := ℝ) hfθ (c θ))
    _ = inner ℝ (c θ) (-(∫ t in Icc a b, φ t • g (θ, t))) := congrArg _ hwθ
    _ = -(∫ t in Icc a b, φ t * inner ℝ (c θ) (g (θ, t))) := by
      rw [inner_neg_right, ← integral_inner (𝕜 := ℝ) hgθ (c θ)]
      simp only [inner_smul_right]
      rfl


/-- Finite-measure L2 weak data determine exactly one continuous map
whose interior values represent the original spatial slices almost everywhere. -/
theorem exists_unique_finite_lp_continuous_representative_of_raw_time_identity
    {α : Type*} [MeasurableSpace α] {q : ℕ}
    (σ : Measure α) [IsFiniteMeasure σ] [IsSeparable σ] {a b : ℝ} (hab : a < b)
    {f g : α × ℝ → Ambient q}
    (hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b))))
    (hg : MemLp g 2 (σ.prod (volume.restrict (Icc a b))))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ θ ∂σ,
        (∫ t in Icc a b, deriv φ t • f (θ, t)) =
          -(∫ t in Icc a b, φ t • g (θ, t))) :
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => f (θ, t)) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => f (θ, t)) := by
  obtain ⟨F, G, hF, hG, hFs, _, hweak⟩ :=
    exists_finite_lp_two_time_curves_with_weak_identity σ a b hf hg hw
  have hFI : MemLp F 2 (volume.restrict (Ioo a b)) :=
    hF.mono_measure (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  have hGI : MemLp G 2 (volume.restrict (Ioo a b)) :=
    hG.mono_measure (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  have hweakI : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t, deriv φ t • F t) = -(∫ t, φ t • G t) :=
    fun φ hφ hcφ hsφ => (hweak φ hφ hcφ hsφ).2.2
  obtain ⟨H, hH, _⟩ :=
    banach_interval_weakDerivative_exists_unique_continuous_representative hab hFI hGI hweakI
  have hFsI : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t)) :=
    ae_mono (Measure.restrict_mono_set volume Ioo_subset_Icc_self) hFs
  have hFsV := (ae_restrict_iff' measurableSet_Ioo).mp hFsI
  have hHs : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ => f (θ, t)) 2 σ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => f (θ, t)) := by
    filter_upwards [hH.1, hFsV] with t hHt hFt ht
    obtain ⟨hft, hFtEq⟩ := hFt ht
    exact ⟨hft, (hHt ht).trans hFtEq⟩
  refine ⟨H, hHs, ?_⟩
  intro K hKs
  have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      (K - H) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ)) := by
    filter_upwards [hKs, hHs] with t hKt hHt ht
    obtain ⟨hKtL, hKtEq⟩ := hKt ht
    obtain ⟨hHtL, hHtEq⟩ := hHt ht
    have heq : hKtL.toLp (fun θ => f (θ, t)) = hHtL.toLp (fun θ => f (θ, t)) :=
      hKtL.toLp_congr hHtL (Filter.EventuallyEq.rfl)
    change K ⟨t, ht.1.le, ht.2.le⟩ - H ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ))
    rw [mem_singleton_iff, sub_eq_zero]
    exact hKtEq.trans (heq.trans hHtEq.symm)
  have hclosed := continuous_interval_mem_closed_of_ae hab (K - H) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro t
  exact sub_eq_zero.mp (Set.mem_singleton_iff.mp (hclosed t))

end StratificationTheory
