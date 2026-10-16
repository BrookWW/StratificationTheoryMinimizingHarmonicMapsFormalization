module

public import StratificationTheory.Interpolation.CylinderLinearInterpolation
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# The full weak gradient of ambient affine cylinder interpolation

Actual finite spatial Sobolev maps lift to the cylinder and multiply by
smooth affine time coefficients. The spatial columns interpolate their
original weak columns, and the time column is the endpoint difference
divided by the interval length.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff

namespace StratificationTheory

/-- On a finite-measure open domain, an actual smooth scalar multiplier with
bounded value and coordinate derivatives obeys the distributional product
rule for every weak column. -/
theorem MemW12.smooth_scalar_product {d q : ℕ} (Ω : OpenDomain d)
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

/-- Affine interpolation in physical time has the full displayed finite weak
gradient. Its spatial columns are the affine combinations of the original
weak columns, and its time column is `(v - u) / (b - a)`. -/
theorem MemW12.cylinder_affine_gradient {n q : ℕ} (U : OpenDomain n)
    (hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤) {a b : ℝ} (hab : a < b)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 U u Du) (hv : MemW12 U v Dv) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let α : Domain (n + 1) → ℝ := fun y => ((e y).2 0 - a) / (b - a)
    MemW12
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
      (fun y => (1 - α y) • u (e y).1 + α y • v (e y).1)
      (fun y => Fin.addCases
        (fun i => (1 - α y) • Du (e y).1 i + α y • Dv (e y).1 i)
        (fun _ => (b - a)⁻¹ • (v (e y).1 - u (e y).1))) := by
  intro e α
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hΩfinite : (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ := by
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩfinite
  let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
  let β : Domain (n + 1) → ℝ := fun y => 1 - α y
  have hα : ContDiff ℝ ∞ α := (T.contDiff.sub contDiff_const).div_const (b - a)
  have hβ : ContDiff ℝ ∞ β := contDiff_const.sub hα
  have hDα (y : Domain (n + 1)) : HasFDerivAt α ((b - a)⁻¹ • T) y := by
    change HasFDerivAt (fun z => (T z - a) / (b - a)) ((b - a)⁻¹ • T) y
    simpa only [div_eq_mul_inv] using (T.hasFDerivAt.sub_const a).mul_const (b - a)⁻¹
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
  have hdα (i : Fin (n + 1)) (y : Domain (n + 1)) :
      coordinateDerivative α hα i y = ((b - a)⁻¹ • T) (EuclideanSpace.single i 1) := by
    change fderiv ℝ α y (EuclideanSpace.single i 1) = _
    rw [(hDα y).fderiv]
  have hdβ (i : Fin (n + 1)) (y : Domain (n + 1)) :
      coordinateDerivative β hβ i y = (-((b - a)⁻¹ • T)) (EuclideanSpace.single i 1) := by
    change fderiv ℝ β y (EuclideanSpace.single i 1) = _
    rw [(hDβ y).fderiv]
  have hdαL (i : Fin (n + 1)) :
      MemLp (coordinateDerivative α hα i) ∞ (volume.restrict Ω.val) := by
    rw [show coordinateDerivative α hα i =
      (fun _ => ((b - a)⁻¹ • T) (EuclideanSpace.single i 1)) from funext (hdα i)]
    exact memLp_const _
  have hdβL (i : Fin (n + 1)) :
      MemLp (coordinateDerivative β hβ i) ∞ (volume.restrict Ω.val) := by
    rw [show coordinateDerivative β hβ i =
      (fun _ => (-((b - a)⁻¹ • T)) (EuclideanSpace.single i 1)) from funext (hdβ i)]
    exact memLp_const _
  have hfirst := MemW12.smooth_scalar_product Ω
    (MemW12.cylinder_lift U hUfinite a b hu) hβ hβL hdβL
  have hsecond := MemW12.smooth_scalar_product Ω
    (MemW12.cylinder_lift U hUfinite a b hv) hα hαL hdαL
  have hsum := hfirst.sub ((HarmonicMaps.MemW12.zero Ω).sub hsecond)
  have hmaps : ((fun y => β y • u (e y).1) - (0 - fun y => α y • v (e y).1)) =
      (fun y => (1 - α y) • u (e y).1 + α y • v (e y).1) := by
    funext y
    change β y • u (e y).1 - (0 - α y • v (e y).1) = _
    rw [zero_sub, sub_neg_eq_add]
  rw [hmaps] at hsum
  have hTsp (i : Fin n) : T (EuclideanSpace.single (Fin.castAdd 1 i) 1) = 0 := by
    change (e (EuclideanSpace.single (Fin.castAdd 1 i) 1)).2 0 = 0
    rw [finAddEquivProd_spatial_basis]
    rfl
  have hTtime (i : Fin 1) : T (EuclideanSpace.single (Fin.natAdd n i) 1) = 1 := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)).2 0 = 1
    rw [finAddEquivProd_time_basis]
    simp only [PiLp.single_apply, ite_true]
  apply hsum.congr_ae (EventuallyEq.refl _ _)
  apply Eventually.of_forall
  intro y
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [hdα, hdβ, neg_apply, smul_apply,
      hTsp, smul_zero, neg_zero, zero_smul, Fin.addCases_left, zero_add, Pi.zero_apply,
      zero_sub, sub_neg_eq_add, β]
    rfl
  · simp only [hdα, hdβ, neg_apply, smul_apply,
      hTtime, smul_eq_mul, mul_one, Fin.addCases_right, smul_zero, add_zero,
      Pi.zero_apply, zero_sub, sub_neg_eq_add, neg_smul, smul_sub]
    abel

end StratificationTheory
