module

public import HarmonicMaps.Analysis.SobolevCutoff

/-!
# Compact cutoffs of local Sobolev maps

A smooth scalar cutoff whose support is compactly contained in an open domain
turns local Sobolev data into finite Sobolev data on the entire Euclidean space.
The displayed global gradient is the ordinary product gradient.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

private theorem integrable_smul_of_compactSupport {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {f : Domain n → E} {χ : Domain n → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume) (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    Integrable (fun x => χ x • f x) volume := by
  have hfK : IntegrableOn f (tsupport χ) volume :=
    hf.integrableOn_compact_subset hsχ hcχ
  have hχK : MemLp χ ∞ (volume.restrict (tsupport χ)) :=
    hχ.memLp_top_of_hasCompactSupport hcχ _
  have hpairK : IntegrableOn (fun x => χ x • f x) (tsupport χ) volume :=
    hfK.smul_of_top_right hχK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpairK
  intro x hx
  by_contra hnot
  have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  simp only [Function.mem_support, hzero, zero_smul] at hx
  exact hx rfl

private theorem memLp_smul_of_support_subset_compact {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {f : Domain n → E} (hf : LocallyMemL2 Ω f)
    {K : Set (Domain n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω.val)
    {χ : Domain n → ℝ} (hχ : MemLp χ ∞ volume)
    (hsχ : Function.support χ ⊆ K) :
    MemLp (fun x => χ x • f x) 2 volume := by
  have hfK : MemLp (K.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (hf K hK hKΩ)
  have hprod := hfK.smul (r := (2 : ℝ≥0∞)) hχ
  convert hprod using 1
  funext x
  change χ x • f x = χ x • (K.indicator f) x
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx]
  · have hzero : χ x = 0 := by
      by_contra hne
      exact hx (hsχ hne)
    simp only [hzero, zero_smul]

/-- Multiplying a map with a weak gradient by an interior compact smooth cutoff gives
a global weak gradient with the scalar product rule. -/
theorem HasWeakGradient.smoothCutoff_univ {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω.val) :
    HasWeakGradient (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => χ x • u x)
      (fun x i => coordinateDerivative χ hχ i x • u x + χ x • Du x i) := by
  have hdχcont (i : Fin n) : Continuous (coordinateDerivative χ hχ i) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdχcompact (i : Fin n) : HasCompactSupport (coordinateDerivative χ hχ i) :=
    hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hdχsupport (i : Fin n) : tsupport (coordinateDerivative χ hχ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsχ
  have huI : Integrable (fun x => χ x • u x) volume :=
    integrable_smul_of_compactSupport hu.1 hχ.continuous hcχ hsχ
  have hdχuI (i : Fin n) :
      Integrable (fun x => coordinateDerivative χ hχ i x • u x) volume :=
    integrable_smul_of_compactSupport hu.1 (hdχcont i) (hdχcompact i) (hdχsupport i)
  have hχDuI (i : Fin n) : Integrable (fun x => χ x • Du x i) volume :=
    integrable_smul_of_compactSupport (hu.2.1 i) hχ.continuous hcχ hsχ
  refine ⟨huI.locallyIntegrable.locallyIntegrableOn univ,
    fun i => ((hdχuI i).add (hχDuI i)).locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro i φ hφ hcφ _
  have hprod : ContDiff ℝ ∞ (fun x => φ x * χ x) := hφ.mul hχ
  have hcprod : HasCompactSupport (fun x => φ x * χ x) := hcχ.mul_left
  have hsprod : tsupport (fun x => φ x * χ x) ⊆ Ω.val :=
    tsupport_mul_subset_right.trans hsχ
  have hibp := hu.2.2 i (fun x => φ x * χ x) hprod hcprod hsprod
  have hφL : MemLp φ ∞ volume :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ volume
  have hdφL : MemLp (coordinateDerivative φ hφ i) ∞ volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) volume
  have hA : Integrable
      (fun x => coordinateDerivative φ hφ i x • (χ x • u x)) volume :=
    huI.smul_of_top_right hdφL
  have hB : Integrable
      (fun x => φ x • (coordinateDerivative χ hχ i x • u x)) volume :=
    (hdχuI i).smul_of_top_right hφL
  have hC : Integrable (fun x => φ x • (χ x • Du x i)) volume :=
    (hχDuI i).smul_of_top_right hφL
  have hχzero (x : Domain n) (hx : x ∉ Ω.val) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsχ hmem))
  have hdχzero (x : Domain n) (hx : x ∉ Ω.val) : coordinateDerivative χ hχ i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem => hx (hdχsupport i hmem))
  simp_rw [coordinateDerivative_mul hφ hχ, add_smul, mul_smul] at hibp
  have hleft : (∫ x in Ω.val,
      coordinateDerivative φ hφ i x • (χ x • u x) +
        φ x • (coordinateDerivative χ hχ i x • u x)) =
      ∫ x, coordinateDerivative φ hφ i x • (χ x • u x) +
        φ x • (coordinateDerivative χ hχ i x • u x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [hχzero x hx, hdχzero x hx, zero_smul, smul_zero, add_zero]
  have hright : (∫ x in Ω.val, φ x • (χ x • Du x i)) =
      ∫ x, φ x • (χ x • Du x i) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [hχzero x hx, zero_smul, smul_zero]
  rw [hleft, hright, integral_add hA hB] at hibp
  change (∫ x in univ, coordinateDerivative φ hφ i x • (χ x • u x)) =
    -(∫ x in univ,
      φ x • (coordinateDerivative χ hχ i x • u x + χ x • Du x i))
  simp only [Measure.restrict_univ]
  simp_rw [smul_add]
  rw [integral_add hB hC]
  apply eq_neg_iff_add_eq_zero.mpr
  calc
    _ = ((∫ x, coordinateDerivative φ hφ i x • (χ x • u x)) +
        ∫ x, φ x • (coordinateDerivative χ hχ i x • u x)) +
        ∫ x, φ x • (χ x • Du x i) := (add_assoc _ _ _).symm
    _ = 0 := by rw [hibp, neg_add_cancel]

/-- An interior compact smooth cutoff of actual local Sobolev data belongs to
finite W1,2 on the whole domain, with its genuine product gradient. -/
theorem MemW12Loc.smoothCutoff_univ {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω.val) :
    MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => χ x • u x)
      (fun x i => coordinateDerivative χ hχ i x • u x + χ x • Du x i) := by
  have hχL : MemLp χ ∞ volume :=
    hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  have hdχL (i : Fin n) : MemLp (coordinateDerivative χ hχ i) ∞ volume :=
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)) volume
  have hχsupport : Function.support χ ⊆ tsupport χ := subset_tsupport χ
  have hdχsupport (i : Fin n) :
      Function.support (coordinateDerivative χ hχ i) ⊆ tsupport χ :=
    (subset_tsupport (coordinateDerivative χ hχ i)).trans
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
  have huL : MemLp (fun x => χ x • u x) 2 volume :=
    memLp_smul_of_support_subset_compact hu.2.1 hcχ hsχ hχL hχsupport
  have hDuL (i : Fin n) : MemLp
      (fun x => coordinateDerivative χ hχ i x • u x + χ x • Du x i) 2 volume :=
    (memLp_smul_of_support_subset_compact hu.2.1 hcχ hsχ (hdχL i) (hdχsupport i)).add
      (memLp_smul_of_support_subset_compact (hu.2.2 i) hcχ hsχ hχL hχsupport)
  exact ⟨hu.1.smoothCutoff_univ hχ hcχ hsχ, by simpa only [Measure.restrict_univ] using huL,
    fun i => by simpa only [Measure.restrict_univ] using hDuL i⟩

end HarmonicMaps
