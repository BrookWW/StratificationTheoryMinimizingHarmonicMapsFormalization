module

public import StratificationTheory.Foundation.CylinderTimeTests
public import StratificationTheory.Foundation.CylinderSobolevCollar
public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Foundation.CylinderLinearL2
public import HarmonicMaps.Analysis.SobolevCutoff
public import HarmonicMaps.Analysis.SobolevDifference
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ambient affine interpolation on a cylinder

Spatial Sobolev maps lift to the full Euclidean cylinder with their original
spatial weak columns and zero time column. Smooth affine time coefficients
then produce an ambient connector between two actual sphere Sobolev maps.
The connector has native surface L2 and one finite radial weak extension on
a common spatial collar; no target-valuedness or distance estimate is asserted.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal

namespace StratificationTheory

private noncomputable def cylinderEquiv (n : ℕ) : Domain (n + 1) ≃L[ℝ] Domain n × ℝ :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n))
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

private theorem cylinderEquiv_apply (n : ℕ) (y : Domain (n + 1)) :
    cylinderEquiv n y =
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1,
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0) := rfl

private theorem cylinderEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (cylinderEquiv n) volume
      ((volume : Measure (Domain n)).prod (volume : Measure ℝ)) :=
  measurePreserving_cylinder_coordinates n

/-- Every spatial coordinate vector remains a spatial coordinate vector under
the physical spatial-time coordinate split. -/
theorem finAddEquivProd_spatial_basis (n : ℕ) (i : Fin n) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (EuclideanSpace.single (Fin.castAdd 1 i) (1 : ℝ)) =
        (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

private theorem cylinderEquiv_spatial_basis (n : ℕ) (i : Fin n) :
    cylinderEquiv n (EuclideanSpace.single (Fin.castAdd 1 i) (1 : ℝ)) =
      (EuclideanSpace.single i 1, 0) := by
  rw [cylinderEquiv_apply, finAddEquivProd_spatial_basis]
  rfl

private theorem cylinderEquiv_time_basis (n : ℕ) :
    cylinderEquiv n (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) (1 : ℝ)) =
      (0, 1) := by
  rw [cylinderEquiv_apply, finAddEquivProd_time_basis]
  simp

private theorem cylinder_spatial_slice_derivative {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (i : Fin n)
    (x : Domain n) :
    coordinateDerivative (fun z => φ ((cylinderEquiv n).symm (z, t)))
      (hφ.comp ((cylinderEquiv n).symm.contDiff.comp
        (contDiff_id.prodMk contDiff_const))) i x =
      coordinateDerivative φ hφ (Fin.castAdd 1 i) ((cylinderEquiv n).symm (x, t)) := by
  let c := cylinderEquiv n
  have h := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
    (c.symm.hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)))
  change fderiv ℝ (fun z => φ (c.symm (z, t))) x (EuclideanSpace.single i 1) = _
  have hd := h.fderiv
  dsimp only [Function.comp_def, id_eq] at hd
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  have hb : c.symm (EuclideanSpace.single i 1, 0) =
      EuclideanSpace.single (Fin.castAdd 1 i) 1 := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact (cylinderEquiv_spatial_basis n i).symm
  change fderiv ℝ φ (c.symm (x, t)) (c.symm (EuclideanSpace.single i 1, 0)) = _
  rw [hb]
  rfl

private theorem cylinder_spatial_slice_compact {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hcφ : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x : Domain n => φ ((cylinderEquiv n).symm (x, t))) := by
  let c := cylinderEquiv n
  have hsub := tsupport_comp_subset_preimage (f := fun x : Domain n => c.symm (x, t)) φ
    (c.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hcompact : IsCompact (Prod.fst '' (c '' tsupport φ)) :=
    (hcφ.image c.continuous).image continuous_fst
  apply hcompact.of_isClosed_subset isClosed_closure
  intro x hx
  exact ⟨(x, t), ⟨c.symm (x, t), hsub hx, c.apply_symm_apply _⟩, rfl⟩

private theorem memLp_cylinder_lift {n q : ℕ} (U : OpenDomain n) (a b : ℝ)
    {u : Domain n → Ambient q} (hu : MemLp u 2 (volume.restrict U.val)) :
    MemLp (fun y : Domain (n + 1) => u (cylinderEquiv n y).1) 2
      (volume.restrict ((cylinderEquiv n) ⁻¹' (U.val ×ˢ Ioo a b))) := by
  have hp := (cylinderEquiv_measurePreserving n).restrict_preimage
    (U.property.measurableSet.prod (measurableSet_Ioo (a := a) (b := b)))
  rw [← Measure.prod_restrict] at hp
  exact (hu.comp_fst (volume.restrict (Ioo a b))).comp_measurePreserving hp

private theorem memW12_cylinder_lift_aux {n q : ℕ} (U : OpenDomain n)
    (hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤) (a b : ℝ)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 U u Du) :
    MemW12
      ⟨(cylinderEquiv n) ⁻¹' (U.val ×ˢ Ioo a b),
        (U.property.prod isOpen_Ioo).preimage (cylinderEquiv n).continuous⟩
      (fun y => u (cylinderEquiv n y).1)
      (fun y => Fin.addCases (fun i => Du (cylinderEquiv n y).1 i) (fun _ => 0)) := by
  let c := cylinderEquiv n
  let Ω : OpenDomain (n + 1) := ⟨c ⁻¹' (U.val ×ˢ Ioo a b),
    (U.property.prod isOpen_Ioo).preimage c.continuous⟩
  let μ := (volume : Measure (Domain n)).restrict U.val
  let ν := (volume : Measure ℝ).restrict (Ioo a b)
  let W : Domain (n + 1) → Ambient q := fun y => u (c y).1
  let DW : Domain (n + 1) → Gradient (n + 1) q :=
    fun y => Fin.addCases (fun i => Du (c y).1 i) (fun _ => 0)
  have hp : MeasurePreserving c (volume.restrict Ω.val) (μ.prod ν) := by
    have h := (cylinderEquiv_measurePreserving n).restrict_preimage
      (U.property.measurableSet.prod (measurableSet_Ioo (a := a) (b := b)))
    rw [← Measure.prod_restrict] at h
    exact h
  have hΩfinite : (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ := by
    change (volume : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} ≠ ⊤
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩfinite
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hUfinite
  have hWL : MemLp W 2 (volume.restrict Ω.val) := memLp_cylinder_lift U a b hu.2.1
  have hDWL (i : Fin (n + 1)) : MemLp (fun y => DW y i) 2 (volume.restrict Ω.val) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [DW, Fin.addCases_left] using memLp_cylinder_lift U a b (hu.2.2 j)
    · simp only [DW, Fin.addCases_right]
      exact MemLp.zero
  have hWI : Integrable W (volume.restrict Ω.val) := hWL.integrable (by norm_num)
  have hDWI (i : Fin (n + 1)) : Integrable (fun y => DW y i) (volume.restrict Ω.val) :=
    (hDWL i).integrable (by norm_num)
  refine ⟨⟨IntegrableOn.locallyIntegrableOn hWI,
    fun i => IntegrableOn.locallyIntegrableOn (hDWI i), ?_⟩, hWL, hDWL⟩
  intro i φ hφ hcφ hsφ
  have hφtop : MemLp φ ∞ (volume.restrict Ω.val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφtop (j : Fin (n + 1)) :
      MemLp (coordinateDerivative φ hφ j) ∞ (volume.restrict Ω.val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single j 1)) _
  have hA (j : Fin (n + 1)) : Integrable
      (fun y => coordinateDerivative φ hφ j y • W y) (volume.restrict Ω.val) :=
    hWI.smul_of_top_right (hdφtop j)
  have hB (j : Fin (n + 1)) : Integrable
      (fun y => φ y • DW y j) (volume.restrict Ω.val) :=
    (hDWI j).smul_of_top_right hφtop
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · let A : Domain n × ℝ → Ambient q := fun p =>
      coordinateDerivative φ hφ (Fin.castAdd 1 j) (c.symm p) • u p.1
    let B : Domain n × ℝ → Ambient q := fun p => φ (c.symm p) • Du p.1 j
    have hp' : MeasurePreserving c.symm (μ.prod ν) (volume.restrict Ω.val) :=
      hp.symm c.toHomeomorph.toMeasurableEquiv
    have hAi : Integrable A (μ.prod ν) := by
      simpa only [Function.comp_def, W, c.apply_symm_apply] using
        hp'.integrable_comp_of_integrable (hA (Fin.castAdd 1 j))
    have hBi : Integrable B (μ.prod ν) := by
      simpa only [Function.comp_def, DW, c.apply_symm_apply, Fin.addCases_left] using
        hp'.integrable_comp_of_integrable (hB (Fin.castAdd 1 j))
    have hslice (t : ℝ) : (∫ x, A (x, t) ∂μ) = -(∫ x, B (x, t) ∂μ) := by
      let ψ : Domain n → ℝ := fun x => φ (c.symm (x, t))
      have hψ : ContDiff ℝ ∞ ψ := hφ.comp
        (c.symm.contDiff.comp (contDiff_id.prodMk contDiff_const))
      have hcψ : HasCompactSupport ψ := cylinder_spatial_slice_compact hcφ t
      have hsψ : tsupport ψ ⊆ U.val := by
        intro x hx
        have ht := tsupport_comp_subset_preimage
          (f := fun x : Domain n => c.symm (x, t)) φ
          (c.symm.continuous.comp (continuous_id.prodMk continuous_const)) hx
        have hΩ := hsφ ht
        change (c (c.symm (x, t))) ∈ U.val ×ˢ Ioo a b at hΩ
        rw [c.apply_symm_apply] at hΩ
        exact hΩ.1
      have h := hu.1.2.2 j ψ hψ hcψ hsψ
      have heq (x : Domain n) : coordinateDerivative ψ hψ j x =
          coordinateDerivative φ hφ (Fin.castAdd 1 j) (c.symm (x, t)) :=
        cylinder_spatial_slice_derivative hφ t j x
      simpa only [heq, ψ] using h
    have ha := hp.integral_comp c.toHomeomorph.measurableEmbedding A
    have hb := hp.integral_comp c.toHomeomorph.measurableEmbedding B
    change (∫ y in Ω.val, coordinateDerivative φ hφ (Fin.castAdd 1 j) y • W y) =
      -(∫ y in Ω.val, φ y • DW y (Fin.castAdd 1 j))
    calc
      _ = ∫ p, A p ∂(μ.prod ν) := by
        simpa only [Function.comp_def, A, c.symm_apply_apply, W] using ha
      _ = ∫ t, ∫ x, A (x, t) ∂μ ∂ν := integral_prod_symm A hAi
      _ = -(∫ t, ∫ x, B (x, t) ∂μ ∂ν) := by
        simp_rw [hslice, integral_neg]
      _ = -(∫ p, B p ∂(μ.prod ν)) := by rw [integral_prod_symm B hBi]
      _ = _ := by
        congr 1
        simpa only [Function.comp_def, B, c.symm_apply_apply, DW, Fin.addCases_left] using hb.symm
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    let k : Fin (n + 1) := Fin.natAdd n (0 : Fin 1)
    have hAsupport : Function.support (fun y => coordinateDerivative φ hφ k y • W y) ⊆ Ω.val := by
      intro y hy
      apply hsφ
      apply tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)
      apply subset_tsupport (coordinateDerivative φ hφ k)
      intro hz
      exact hy (by simp only [hz, zero_smul])
    have hFsupport : Function.support (fun y => φ y • W y) ⊆ Ω.val :=
      (Function.support_smul_subset_left _ _).trans ((subset_tsupport φ).trans hsφ)
    have hAg : Integrable (fun y => coordinateDerivative φ hφ k y • W y) volume :=
      (integrableOn_iff_integrable_of_support_subset hAsupport).mp (hA k)
    have hFg : Integrable (fun y => φ y • W y) volume :=
      (integrableOn_iff_integrable_of_support_subset hFsupport).mp
        (hWI.smul_of_top_right hφtop)
    have hline (y : Domain (n + 1)) : HasLineDerivAt ℝ W 0 y (EuclideanSpace.single k 1) := by
      change HasDerivAt (fun t : ℝ => u (c (y + t • EuclideanSpace.single k 1)).1) 0 0
      have heq : (fun t : ℝ => u (c (y + t • EuclideanSpace.single k 1)).1) =
          (fun _ => u (c y).1) := by
        funext t
        rw [map_add, map_smul]
        change u ((c y).1 + t • (c (EuclideanSpace.single k 1)).1) = _
        rw [cylinderEquiv_time_basis]
        simp only [smul_zero, add_zero]
      rw [heq]
      exact hasDerivAt_const _ _
    have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (f := φ) (f' := coordinateDerivative φ hφ k) (g := W) (g' := fun _ => 0)
      (v := EuclideanSpace.single k 1)
      (B := ContinuousLinearMap.lsmul ℝ ℝ)
      hAg (by simp only [ContinuousLinearMap.lsmul_apply, smul_zero]; exact integrable_zero _ _ _) hFg
      (fun y _ => ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).hasLineDerivAt _)
      (fun y _ => hline y)
    have hzero : (∫ y, coordinateDerivative φ hφ k y • W y) = 0 := by
      simpa only [ContinuousLinearMap.lsmul_apply, smul_zero, integral_zero, neg_eq_zero] using hibp.symm
    change (∫ y in Ω.val, coordinateDerivative φ hφ k y • W y) =
      -(∫ y in Ω.val, φ y • DW y k)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy =>
      Function.notMem_support.mp (fun hz => hy (hAsupport hz)))]
    simpa only [DW, k, Fin.addCases_right, smul_zero, integral_zero, neg_zero] using hzero

/-- A finite spatial Sobolev map has a genuine constant-in-time extension on
any bounded open time interval, with every spatial column retained and its
time column equal to zero. -/
theorem MemW12.cylinder_lift {n q : ℕ} (U : OpenDomain n)
    (hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤) (a b : ℝ)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 U u Du) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MemW12
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
      (fun y => u (e y).1)
      (fun y => Fin.addCases (fun i => Du (e y).1 i) (fun _ => 0)) :=
  memW12_cylinder_lift_aux U hUfinite a b hu

private theorem memW12_smooth_scalar_product {d q : ℕ} (Ω : OpenDomain d)
    [IsFiniteMeasure (volume.restrict Ω.val)]
    {u : Domain d → Ambient q} {Du : Domain d → Gradient d q}
    (hu : MemW12 Ω u Du) {χ : Domain d → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχL : MemLp χ ∞ (volume.restrict Ω.val))
    (hdχL : ∀ i, MemLp (coordinateDerivative χ hχ i) ∞ (volume.restrict Ω.val)) :
    MemW12 Ω (fun x => χ x • u x)
      (fun x i => coordinateDerivative χ hχ i x • u x + χ x • Du x i) := by
  let μ := volume.restrict Ω.val
  have huL : MemLp (fun x => χ x • u x) 2 μ := hu.2.1.smul hχL
  have hDuL (i : Fin d) : MemLp
      (fun x => coordinateDerivative χ hχ i x • u x + χ x • Du x i) 2 μ :=
    (hu.2.1.smul (r := (2 : ℝ≥0∞)) (hdχL i)).add ((hu.2.2 i).smul (r := (2 : ℝ≥0∞)) hχL)
  have huI : IntegrableOn (fun x => χ x • u x) Ω.val :=
    huL.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hDuI (i : Fin d) : IntegrableOn
      (fun x => coordinateDerivative χ hχ i x • u x + χ x • Du x i) Ω.val :=
    (hDuL i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨⟨huI.locallyIntegrableOn,
    fun i => (hDuI i).locallyIntegrableOn, ?_⟩, huL, hDuL⟩
  intro i φ hφ hcφ hsφ
  have hprod : ContDiff ℝ ∞ (fun x => φ x * χ x) := hφ.mul hχ
  have hcprod : HasCompactSupport (fun x => φ x * χ x) := hcφ.mul_right
  have hsprod : tsupport (fun x => φ x * χ x) ⊆ Ω.val :=
    tsupport_mul_subset_left.trans hsφ
  have hibp := hu.1.2.2 i (fun x => φ x * χ x) hprod hcprod hsprod
  have hφL : MemLp φ ∞ μ := hφ.continuous.memLp_top_of_hasCompactSupport hcφ μ
  have hdφL : MemLp (coordinateDerivative φ hφ i) ∞ μ :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) μ
  have hA : Integrable (fun x => coordinateDerivative φ hφ i x • (χ x • u x)) μ :=
    (huL.smul (r := (2 : ℝ≥0∞)) hdφL).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hB : Integrable (fun x => φ x • (coordinateDerivative χ hχ i x • u x)) μ :=
    ((hu.2.1.smul (r := (2 : ℝ≥0∞)) (hdχL i)).smul (r := (2 : ℝ≥0∞)) hφL).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hC : Integrable (fun x => φ x • (χ x • Du x i)) μ :=
    (((hu.2.2 i).smul (r := (2 : ℝ≥0∞)) hχL).smul (r := (2 : ℝ≥0∞)) hφL).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp_rw [coordinateDerivative_mul hφ hχ, add_smul, mul_smul] at hibp
  change (∫ x, coordinateDerivative φ hφ i x • (χ x • u x) +
    φ x • (coordinateDerivative χ hχ i x • u x) ∂μ) =
    -(∫ x, φ x • (χ x • Du x i) ∂μ) at hibp
  rw [integral_add hA hB] at hibp
  change (∫ x, coordinateDerivative φ hφ i x • (χ x • u x) ∂μ) =
    -(∫ x, φ x • (coordinateDerivative χ hχ i x • u x + χ x • Du x i) ∂μ)
  simp_rw [smul_add]
  rw [integral_add hB hC]
  apply eq_neg_iff_add_eq_zero.mpr
  calc
    _ = ((∫ x, coordinateDerivative φ hφ i x • (χ x • u x) ∂μ) +
        ∫ x, φ x • (coordinateDerivative χ hχ i x • u x) ∂μ) +
        ∫ x, φ x • (χ x • Du x i) ∂μ := (add_assoc _ _ _).symm
    _ = 0 := by rw [hibp, neg_add_cancel]

private theorem memW12_cylinder_affine_aux {n q : ℕ} (U : OpenDomain n)
    (hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤) {a b : ℝ} (hab : a < b)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 U u Du) (hv : MemW12 U v Dv) :
    ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
      MemW12
        ⟨(cylinderEquiv n) ⁻¹' (U.val ×ˢ Ioo a b),
          (U.property.prod isOpen_Ioo).preimage (cylinderEquiv n).continuous⟩
        (fun y => (1 - ((cylinderEquiv n y).2 - a) / (b - a)) • u (cylinderEquiv n y).1 +
          (((cylinderEquiv n y).2 - a) / (b - a)) • v (cylinderEquiv n y).1) Dw := by
  let c := cylinderEquiv n
  let Ω : OpenDomain (n + 1) := ⟨c ⁻¹' (U.val ×ˢ Ioo a b),
    (U.property.prod isOpen_Ioo).preimage c.continuous⟩
  have hΩfinite : (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ := by
    change (volume : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} ≠ ⊤
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩfinite
  let T : Domain (n + 1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (Domain n) ℝ).comp c.toContinuousLinearMap
  let α : Domain (n + 1) → ℝ := fun y => (T y - a) / (b - a)
  let β : Domain (n + 1) → ℝ := fun y => 1 - α y
  have hα : ContDiff ℝ ∞ α := (T.contDiff.sub contDiff_const).div_const (b - a)
  have hβ : ContDiff ℝ ∞ β := contDiff_const.sub hα
  have hDα (y : Domain (n + 1)) : HasFDerivAt α ((b - a)⁻¹ • T) y := by
    simpa only [α, div_eq_mul_inv] using (T.hasFDerivAt.sub_const a).mul_const (b - a)⁻¹
  have hDβ (y : Domain (n + 1)) : HasFDerivAt β (-((b - a)⁻¹ • T)) y :=
    (hDα y).const_sub 1
  have hαL : MemLp α ∞ (volume.restrict Ω.val) := by
    apply memLp_top_of_bound hα.continuous.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with y hy
    have ht : a < T y ∧ T y < b := hy.2
    have hlo : 0 ≤ α y := div_nonneg (sub_nonneg.mpr ht.1.le) (sub_pos.mpr hab).le
    have hhi : α y ≤ 1 :=
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2.le a)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  have hβL : MemLp β ∞ (volume.restrict Ω.val) := (memLp_const (1 : ℝ)).sub hαL
  have hdαL (i : Fin (n + 1)) :
      MemLp (coordinateDerivative α hα i) ∞ (volume.restrict Ω.val) := by
    have heq : coordinateDerivative α hα i =
        fun _ => ((b - a)⁻¹ • T) (EuclideanSpace.single i 1) := by
      funext y
      change fderiv ℝ α y (EuclideanSpace.single i 1) = _
      rw [(hDα y).fderiv]
    rw [heq]
    exact memLp_const _
  have hdβL (i : Fin (n + 1)) :
      MemLp (coordinateDerivative β hβ i) ∞ (volume.restrict Ω.val) := by
    have heq : coordinateDerivative β hβ i =
        fun _ => (-((b - a)⁻¹ • T)) (EuclideanSpace.single i 1) := by
      funext y
      change fderiv ℝ β y (EuclideanSpace.single i 1) = _
      rw [(hDβ y).fderiv]
    rw [heq]
    exact memLp_const _
  have hfirst := memW12_smooth_scalar_product Ω
    (memW12_cylinder_lift_aux U hUfinite a b hu) hβ hβL hdβL
  have hsecond := memW12_smooth_scalar_product Ω
    (memW12_cylinder_lift_aux U hUfinite a b hv) hα hαL hdαL
  have hsum := hfirst.sub ((MemW12.zero Ω).sub hsecond)
  have hmaps : ((fun y => β y • u (cylinderEquiv n y).1) -
      (0 - fun y => α y • v (cylinderEquiv n y).1)) =
      (fun y => (1 - ((cylinderEquiv n y).2 - a) / (b - a)) • u (cylinderEquiv n y).1 +
        (((cylinderEquiv n y).2 - a) / (b - a)) • v (cylinderEquiv n y).1) := by
    funext y
    change β y • u (cylinderEquiv n y).1 - (0 - α y • v (cylinderEquiv n y).1) = _
    rw [zero_sub, sub_neg_eq_add]
    rfl
  rw [hmaps] at hsum
  exact ⟨_, hsum⟩

/-- Affine interpolation between two genuine sphere Sobolev maps belongs to
the full physical cylinder Sobolev space, including native surface L2 and a
single finite radial extension with all spatial and temporal weak columns. -/
theorem memCylinderW12_linearInterpolation {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) {u v : sphere (0 : Domain n) 1 → Ambient q}
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MemCylinderW12 hn hab (fun c : unitCylinder n a b =>
      (1 - ((e c.val).2 0 - a) / (b - a)) • u ⟨(e c.val).1, c.property.1⟩ +
        (((e c.val).2 0 - a) / (b - a)) • v ⟨(e c.val).1, c.property.1⟩) := by
  intro e
  have hL := memLp_two_unitCylinder_linearInterpolation (by omega : 0 < n) hab hu.1 hv.1
  obtain ⟨_, U, hUS, _hUzero, f, Df, hf, hfu⟩ := hu
  obtain ⟨_, V, hVS, _hVzero, g, Dg, hg, hgv⟩ := hv
  let O : OpenDomain n := ⟨U.val ∩ V.val, U.property.inter V.property⟩
  have hOS : sphere (0 : Domain n) 1 ⊆ O.val := fun x hx => ⟨hUS hx, hVS hx⟩
  obtain ⟨δ, hδ, hδsmall, hsub⟩ := exists_radial_collar_subset O hOS
  let C : OpenDomain n := ⟨{x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ},
    isOpen_radial_collar δ⟩
  have hCU : C.val ⊆ U.val := fun x hx => (hsub hx).1
  have hCV : C.val ⊆ V.val := fun x hx => (hsub hx).2
  have hfC : MemW12 C f Df :=
    ⟨hf.1.mono hCU, hf.2.1.mono_measure (Measure.restrict_mono_set volume hCU),
      fun i => (hf.2.2 i).mono_measure (Measure.restrict_mono_set volume hCU)⟩
  have hgC : MemW12 C g Dg :=
    ⟨hg.1.mono hCV, hg.2.1.mono_measure (Measure.restrict_mono_set volume hCV),
      fun i => (hg.2.2 i).mono_measure (Measure.restrict_mono_set volume hCV)⟩
  have hCfinite : (volume : Measure (Domain n)) C.val ≠ ⊤ := by
    have hCb : C.val ⊆ ball (0 : Domain n) (1 + δ) :=
      fun x hx => mem_ball_zero_iff.mpr hx.2
    exact (lt_of_le_of_lt (measure_mono hCb) measure_ball_lt_top).ne
  obtain ⟨Dw, hw⟩ := memW12_cylinder_affine_aux C hCfinite hab hfC hgC
  refine ⟨hL, C, sphere_subset_radial_collar hδ,
    zero_not_mem_radial_collar (by linarith only [hδsmall]),
    (fun y => (1 - ((e y).2 0 - a) / (b - a)) • f (e y).1 +
      (((e y).2 0 - a) / (b - a)) • g (e y).1), Dw, hw, ?_⟩
  intro ρ z _ht hx
  change (1 - ((e (e.symm (ρ.val • (e z.val).1, (e z.val).2))).2 0 - a) / (b - a)) •
      f (e (e.symm (ρ.val • (e z.val).1, (e z.val).2))).1 +
    (((e (e.symm (ρ.val • (e z.val).1, (e z.val).2))).2 0 - a) / (b - a)) •
      g (e (e.symm (ρ.val • (e z.val).1, (e z.val).2))).1 = _
  rw [e.apply_symm_apply]
  rw [hfu ρ ⟨(e z.val).1, z.property.1⟩ (hCU hx),
    hgv ρ ⟨(e z.val).1, z.property.1⟩ (hCV hx)]

end StratificationTheory
