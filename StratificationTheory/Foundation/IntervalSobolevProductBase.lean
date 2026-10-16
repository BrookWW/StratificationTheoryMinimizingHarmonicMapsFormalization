module

public import StratificationTheory.Foundation.ClosedTargetACLLineEstimates
public import StratificationTheory.Foundation.CylinderCoordinateMeasure

/-!
# A native one-dimensional Sobolev graph from integral data

The original real-line L2 data and their exact integral increments produce
the finite weak graph in the one-coordinate Euclidean model.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff
namespace StratificationTheory

/-- A bounded interval has finite native volume in the one-coordinate model. -/
theorem volume_domainOne_interval_ne_top (a b : ℝ) :
    (volume : Measure (Domain 1)) {x | x 0 ∈ Ioo a b} ≠ ⊤ := by
  have hm := measurePreserving_domainOne_eval.measure_preimage
    (measurableSet_Ioo (a := a) (b := b)).nullMeasurableSet
  change (volume : Measure (Domain 1)) {x | x 0 ∈ Ioo a b} =
    (volume : Measure ℝ) (Ioo a b) at hm
  rw [hm, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- Evaluation at the sole coordinate identifies the actual restricted
Euclidean integral with the original real interval integral. -/
theorem integral_domainOne_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (a b : ℝ) (f : ℝ → E) :
    (∫ x : Domain 1 in {x | x 0 ∈ Ioo a b}, f (x 0)) =
      ∫ t in Ioo a b, f t := by
  have hm := measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := a) (b := b))
  exact hm.integral_comp
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph.measurableEmbedding f

/-- A representative with the original L2 class and original integral
increments is a genuine one-dimensional finite Sobolev map. -/
theorem memW12_domainOne_of_integral_increments {q : ℕ}
    {a b : ℝ} (hab : a < b) {F f g : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y) :
    MemW12
      ⟨{x : Domain 1 | x 0 ∈ Ioo a b},
        isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous⟩
      (fun x => F (x 0)) (fun x _ => g (x 0)) := by
  let O : OpenDomain 1 := ⟨{x : Domain 1 | x 0 ∈ Ioo a b},
    isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous⟩
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hτ := measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := a) (b := b))
  have hF : MemLp (fun x : Domain 1 => F (x 0)) 2 (volume.restrict O.val) :=
    (hf.ae_eq hFae.symm).comp_measurePreserving hτ
  have hD : MemLp (fun x : Domain 1 => g (x 0)) 2 (volume.restrict O.val) :=
    hg.comp_measurePreserving hτ
  have hfinite : (volume : Measure (Domain 1)) O.val ≠ ⊤ :=
    volume_domainOne_interval_ne_top a b
  letI : IsFiniteMeasure (volume.restrict O.val) := isFiniteMeasure_restrict.mpr hfinite
  have hFI : IntegrableOn (fun x : Domain 1 => F (x 0)) O.val volume :=
    hF.integrable (by norm_num)
  have hDI : IntegrableOn (fun x : Domain 1 => g (x 0)) O.val volume :=
    hD.integrable (by norm_num)
  refine ⟨⟨hFI.locallyIntegrableOn,
    fun _ => hDI.locallyIntegrableOn, ?_⟩, hF, fun _ => hD⟩
  intro i ψ hψ hcψ hsψ
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let φ : ℝ → ℝ := ψ ∘ τ.symm
  have hφ : ContDiff ℝ ∞ φ := hψ.comp τ.symm.contDiff
  have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph τ.symm.toHomeomorph
  have hsφ : tsupport φ ⊆ Ioo a b := by
    intro t ht
    have hm := tsupport_comp_subset_preimage (f := τ.symm) ψ τ.symm.continuous ht
    have hO := hsψ hm
    change τ (τ.symm t) ∈ Ioo a b at hO
    simpa only [τ.apply_symm_apply] using hO
  have hdφ (x : Domain 1) : deriv φ (x 0) = coordinateDerivative ψ hψ 0 x := by
    have hτD : HasDerivAt (fun t : ℝ => τ.symm t) (τ.symm 1) (x 0) :=
      τ.symm.hasFDerivAt.hasDerivAt
    have hψD := ((hψ.differentiable (by simp) (τ.symm (x 0))).hasFDerivAt).comp_hasDerivAt
      (x 0) hτD
    have hinv : τ.symm (x 0) = x := τ.symm_apply_apply x
    rw [hinv] at hψD
    have hτone : τ.symm 1 = EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      ext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [τ, PiLp.equivOfUnique]
    simpa only [hτone, coordinateDerivative, Function.comp_def, φ] using hψD.deriv
  have hw := interval_weakDerivative_of_integral_increments hab hg
    (Filter.EventuallyEq.rfl : F =ᵐ[volume.restrict (Ioo a b)] F) hinc φ hφ hcφ hsφ
  have hleft : (∫ t in Ioo a b, deriv φ t • F t) = ∫ t, deriv φ t • F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport
      (fun hm => ht (hsφ (tsupport_deriv_subset hm))), zero_smul]
  have hright : (∫ t in Ioo a b, φ t • g t) = ∫ t, φ t • g t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun hm => ht (hsφ hm)), zero_smul]
  rw [← hleft, ← hright] at hw
  have hL := hτ.integral_comp τ.toHomeomorph.measurableEmbedding (fun t => deriv φ t • F t)
  have hR := hτ.integral_comp τ.toHomeomorph.measurableEmbedding (fun t => φ t • g t)
  change (∫ x in O.val, deriv φ (x 0) • F (x 0)) = _ at hL
  simp_rw [hdφ] at hL
  change (∫ x in O.val, ψ (τ.symm (τ x)) • g (x 0)) = _ at hR
  simp_rw [τ.symm_apply_apply] at hR
  change (∫ x in O.val, coordinateDerivative ψ hψ 0 x • F (x 0)) =
    -(∫ x in O.val, ψ x • g (x 0))
  exact hL.trans (hw.trans (congrArg Neg.neg hR.symm))

end StratificationTheory
