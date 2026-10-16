module

public import StratificationTheory.Foundation.SphericalProjectionDifferential
public import HarmonicMaps.Analysis.SmoothWeakGradient
public import StratificationTheory.Foundation.AngularL2Membership
public import StratificationTheory.Frozen.SphereSobolev
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual smooth radial pullbacks

A smooth Euclidean map pulled back by spherical normalization has its
classical differential as its distributional weak gradient on every open
set avoiding the origin. Its coordinate columns are reciprocal-radius
multiples of the tangential projection of the actual smooth ambient columns.
-/

public section

open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff BigOperators RealInnerProductSpace

namespace StratificationTheory

private theorem radial_test_pairing_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {f : Domain n → E} {φ : Domain n → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω.val) :
    Integrable (fun x => φ x • f x) volume := by
  have hfK : IntegrableOn f (tsupport φ) volume :=
    hf.integrableOn_compact_subset hs hc
  have hφK := hφ.memLp_top_of_hasCompactSupport hc (volume.restrict (tsupport φ))
  have hpair := hfK.smul_of_top_right hφK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpair
  intro x hx
  by_contra hnot
  have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  change φ x • f x ≠ 0 at hx
  exact hx (by rw [hz, zero_smul])

/-- Classical derivatives of a map smooth on the actual open domain satisfy
the literal compact-test weak-gradient identity on that domain. -/
theorem hasWeakGradient_of_contDiffOn {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ ∞ f Ω.val) :
    HasWeakGradient Ω f
      (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  have hfi : LocallyIntegrableOn f Ω.val volume :=
    hf.continuousOn.locallyIntegrableOn Ω.property.measurableSet
  have hdf (i : Fin n) : ContinuousOn
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) Ω.val :=
    (hf.continuousOn_fderiv_of_isOpen Ω.property (by simp)).clm_apply continuousOn_const
  have hdi (i : Fin n) : LocallyIntegrableOn
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) Ω.val volume :=
    (hdf i).locallyIntegrableOn Ω.property.measurableSet
  refine ⟨hfi, hdi, ?_⟩
  intro i φ hφ hcφ hsφ
  have hdφ : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdφ : tsupport (coordinateDerivative φ hφ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ
  have hcdφ : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hpair1 := radial_test_pairing_integrable hfi hdφ hcdφ hsdφ
  have hpair2 := radial_test_pairing_integrable (hdi i) hφ.continuous hcφ hsφ
  have hpair0 := radial_test_pairing_integrable hfi hφ.continuous hcφ hsφ
  have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := φ) (g := f) (v := EuclideanSpace.single i 1)
    hpair1 hpair2 hpair0
    (fun _ _ => (hφ.differentiable (by simp)).differentiableAt)
    (fun x hx => (hf.differentiableOn (by simp)).differentiableAt
      (Ω.property.mem_nhds (hsφ hx)))
  have hleft : (∫ x in Ω.val, coordinateDerivative φ hφ i x • f x) =
      ∫ x, coordinateDerivative φ hφ i x • f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hsdφ hm)), zero_smul]
  have hright : (∫ x in Ω.val, φ x • fderiv ℝ f x (EuclideanSpace.single i 1)) =
      ∫ x, φ x • fderiv ℝ f x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hsφ hm)), zero_smul]
  rw [hleft, hright]
  exact neg_eq_iff_eq_neg.mp hIBP.symm

/-- A smooth ambient map has a smooth degree-zero radial pullback on the
punctured Euclidean domain. -/
theorem contDiffOn_radial_smooth_pullback {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun x : Domain n => f (a + r • (‖x‖⁻¹ • x)))
      ({0}ᶜ : Set (Domain n)) := by
  have hg : ContDiffOn ℝ ∞ (fun x : Domain n => a + r • (‖x‖⁻¹ • x))
      ({0}ᶜ : Set (Domain n)) :=
    (contDiffOn_const (c := a)).add
      ((contDiffOn_const (c := r)).smul contDiffOn_normalization)
  exact hf.comp_contDiffOn hg

/-- The actual classical derivative is the weak gradient of the smooth
radial pullback on every open set avoiding the origin. -/
theorem hasWeakGradient_radial_smooth_pullback {n q : ℕ}
    (U : OpenDomain n) (hU : (0 : Domain n) ∉ U.val)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ) :
    HasWeakGradient U (fun x : Domain n => f (a + r • (‖x‖⁻¹ • x)))
      (fun x i => fderiv ℝ (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y))) x
        (EuclideanSpace.single i 1)) := by
  apply hasWeakGradient_of_contDiffOn
  apply (contDiffOn_radial_smooth_pullback hf a r).mono
  intro x hx
  change x ≠ 0
  exact fun hz => hU (hz ▸ hx)

/-- The literal Fréchet chain rule at an actual nonzero point. -/
theorem hasFDerivAt_radial_smooth_pullback {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ)
    (x : {x : Domain n // x ≠ 0}) :
    HasFDerivAt (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y)))
      ((fderiv ℝ f (a + r • (‖x.val‖⁻¹ • x.val))).comp
        (r • normalizationDifferential x)) x.val := by
  exact ((hf.differentiable (by simp)) _).hasFDerivAt.comp x.val
    ((hasFDerivAt_normalization x).const_smul r |>.const_add a)

private theorem radial_point_ne_zero {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (θ : sphere (0 : Domain n) 1) : ρ • θ.val ≠ 0 := by
  have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
  intro hz
  have := congrArg norm hz
  rw [norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one, norm_zero] at this
  exact hρ.ne' this

private theorem radial_point_norm {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (θ : sphere (0 : Domain n) 1) : ‖ρ • θ.val‖ = ρ := by
  have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
  rw [norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one]

/-- Normalization and hence the smooth pullback have the exact degree-zero
ray values at every positive radius. -/
theorem radial_smooth_pullback_ray {n q : ℕ}
    (f : Domain n → Ambient q) (a : Domain n) (r : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (θ : sphere (0 : Domain n) 1) :
    f (a + r • (‖ρ • θ.val‖⁻¹ • (ρ • θ.val))) = f (a + r • θ.val) := by
  have hn : ‖ρ • θ.val‖⁻¹ • (ρ • θ.val) = θ.val := by
    rw [radial_point_norm hρ θ, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  rw [hn]

private theorem normalizationDifferential_radial_column {n : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (θ : sphere (0 : Domain n) 1) (i : Fin n) :
    normalizationDifferential ⟨ρ • θ.val, radial_point_ne_zero hρ θ⟩
        (EuclideanSpace.single i 1) =
      ρ⁻¹ • (EuclideanSpace.single i 1 - θ.val i • θ.val) := by
  simp only [normalizationDifferential, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    radial_point_norm hρ θ,
    EuclideanSpace.inner_single_right, map_smul, one_mul, conj_trivial]
  simp only [smul_smul, smul_sub, smul_eq_mul]
  have hc : ρ⁻¹ ^ 3 * (ρ * θ.val i * ρ) = ρ⁻¹ * θ.val i := by
    field_simp
  rw [hc]

private theorem radial_smooth_fderiv_apply_eq_sum {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (x v : Domain n) :
    fderiv ℝ f x v = ∑ i : Fin n, v i • coordinateDerivative f hf i x := by
  have hrepr : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    fderiv ℝ f x v = fderiv ℝ f x (∑ i : Fin n, v i • EuclideanSpace.single i 1) :=
      congrArg (fun w => fderiv ℝ f x w) hrepr.symm
    _ = _ := by simp only [map_sum, map_smul, coordinateDerivative]

/-- At an actual positive ray point, the smooth radial pullback derivative
columns are the scaled tangential projection of the ambient columns. -/
theorem fderiv_radial_smooth_pullback_column {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (θ : sphere (0 : Domain n) 1) (i : Fin n) :
    fderiv ℝ (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y)))
        (ρ • θ.val) (EuclideanSpace.single i 1) =
      (r / ρ) • tangentialColumns θ
        (fun j => coordinateDerivative f hf j (a + r • θ.val)) i := by
  have h := (hasFDerivAt_radial_smooth_pullback hf a r
    ⟨ρ • θ.val, radial_point_ne_zero hρ θ⟩).fderiv
  rw [h, ContinuousLinearMap.comp_apply, smul_apply,
    normalizationDifferential_radial_column hρ θ i]
  have hn : ‖ρ • θ.val‖⁻¹ • (ρ • θ.val) = θ.val := by
    rw [radial_point_norm hρ θ, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  simp only [hn, map_smul, map_sub, coordinateDerivative,
    radial_smooth_fderiv_apply_eq_sum hf (a + r • θ.val) θ.val,
    tangentialColumns, smul_smul, div_eq_mul_inv]

/-- The precise HS square of the actual radial pullback gradient. -/
theorem hsNormSq_fderiv_radial_smooth_pullback {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (θ : sphere (0 : Domain n) 1) :
    hsNormSq (fun i => fderiv ℝ (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y)))
        (ρ • θ.val) (EuclideanSpace.single i 1)) =
      (r / ρ) ^ 2 *
        (hsNormSq (fun i => coordinateDerivative f hf i (a + r • θ.val)) -
          ‖∑ j : Fin n, θ.val j • coordinateDerivative f hf j (a + r • θ.val)‖ ^ 2) := by
  simp_rw [hsNormSq, fderiv_radial_smooth_pullback_column hf a r hρ θ,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum]
  exact congrArg (fun t : ℝ => (r / ρ) ^ 2 * t)
    (hsNormSq_tangentialColumns θ
      (fun i => coordinateDerivative f hf i (a + r • θ.val)))

/-- The actual radial pullback HS square is bounded by the ambient HS square
with the exact reciprocal-radius factor. -/
theorem hsNormSq_fderiv_radial_smooth_pullback_le {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (θ : sphere (0 : Domain n) 1) :
    hsNormSq (fun i => fderiv ℝ (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y)))
        (ρ • θ.val) (EuclideanSpace.single i 1)) ≤
      (r / ρ) ^ 2 * hsNormSq (fun i => coordinateDerivative f hf i (a + r • θ.val)) := by
  rw [hsNormSq_fderiv_radial_smooth_pullback hf a r hρ θ]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)

private theorem radial_memLp_of_continuousOn_compact {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Domain n → E} {K : Set (Domain n)}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    MemLp f 2 (volume.restrict K) := by
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  apply MemLp.of_bound (hf.aestronglyMeasurable hK.isClosed.measurableSet) C
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
  exact hC x hx

/-- Smooth radial pullbacks have the literal finite Sobolev membership on
open domains contained in a compact set avoiding the origin. -/
theorem memW12_radial_smooth_pullback {n q : ℕ}
    (U : OpenDomain n) {K : Set (Domain n)} (hK : IsCompact K)
    (hUK : U.val ⊆ K) (hK0 : (0 : Domain n) ∉ K)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ) :
    MemW12 U (fun x : Domain n => f (a + r • (‖x‖⁻¹ • x)))
      (fun x i => fderiv ℝ (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y))) x
        (EuclideanSpace.single i 1)) := by
  have hKP : K ⊆ ({0}ᶜ : Set (Domain n)) := by
    intro x hx
    change x ≠ 0
    exact fun hz => hK0 (hz ▸ hx)
  have hUP := hUK.trans hKP
  have hg := contDiffOn_radial_smooth_pullback hf a r
  have hgK := hg.continuousOn.mono hKP
  have hDg := hg.continuousOn_fderiv_of_isOpen
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (Domain n))) (by simp)
  refine ⟨hasWeakGradient_radial_smooth_pullback U (fun hx => hK0 (hUK hx)) hf a r,
    (radial_memLp_of_continuousOn_compact hK hgK).mono_measure
      (Measure.restrict_mono_set volume hUK), ?_⟩
  intro i
  exact (radial_memLp_of_continuousOn_compact hK
    ((hDg.clm_apply continuousOn_const).mono hKP)).mono_measure
      (Measure.restrict_mono_set volume hUK)

/-- Every actual smooth ambient slice belongs to the literal sphere Sobolev
space, using its degree-zero extension and its actual weak gradient. -/
theorem memSphereW12_smooth_slice {n q : ℕ} (hn : 2 ≤ n)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (a : Domain n) (r : ℝ) :
    MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val)) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hv : Continuous (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val)) :=
    hf.continuous.comp ((continuous_const (y := a)).add
      ((continuous_const (y := r)).smul continuous_subtype_val))
  have hvL : MemLp (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val)) 2
      (volume : Measure (Domain n)).toSphere := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
    exact MemLp.of_bound hv.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun θ => hC θ (mem_univ θ))
  have hU : IsOpen {x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2} :=
    isOpen_Ioo.preimage continuous_norm
  let U : OpenDomain n := ⟨{x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}, hU⟩
  let K : Set (Domain n) := closedBall 0 2 \ ball 0 (1 / 2)
  have hK : IsCompact K := (isCompact_closedBall 0 2).diff isOpen_ball
  have hUK : U.val ⊆ K := by
    intro x hx
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hx.2.le,
      by simpa only [mem_ball, dist_zero_right, not_lt] using hx.1.le⟩
  have hK0 : (0 : Domain n) ∉ K := by
    intro hx
    exact hx.2 (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hsU : sphere (0 : Domain n) 1 ⊆ U.val := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    change 1 / 2 < ‖x‖ ∧ ‖x‖ < 2
    rw [hn]
    norm_num
  refine ⟨?_, U, hsU, (fun hx => hK0 (hUK hx)),
    (fun x => f (a + r • (‖x‖⁻¹ • x))),
    (fun x i => fderiv ℝ (fun y : Domain n => f (a + r • (‖y‖⁻¹ • y))) x
      (EuclideanSpace.single i 1)), memW12_radial_smooth_pullback U hK hUK hK0 hf a r, ?_⟩
  · rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
    exact hvL
  · intro ρ θ _
    exact radial_smooth_pullback_ray f a r ρ.property θ

end StratificationTheory
