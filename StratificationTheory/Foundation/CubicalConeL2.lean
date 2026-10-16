module

public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import StratificationTheory.Foundation.CubicalConeMoments
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual L2 pullback from a face to its positive cone

Original native face L2 data pull back by the literal inverse face coordinates.
The exact value and inverse-square moments give the same map's native L2
integrals, without supplying any cone membership or energy as a premise.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

private theorem weighted_native_cone_l2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict S)) (κ : ℝ → ℝ) (hκ : Measurable κ)
    (hMoment : (∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((κ t) ^ 2)) ≠ ⊤) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ S}
    MemLp (fun y => κ (T y) • f (ξ y)) 2 (volume.restrict C) ∧
    (∫ y in C, ‖κ (T y) • f (ξ y)‖ ^ 2) =
      (∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((κ t) ^ 2)).toReal *
          ∫ x in S, ‖f x‖ ^ 2 := by
  intro e T ξ C
  let μ := (volume : Measure (Domain n)).restrict S
  let ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  let σ := (volume : Measure (Domain (n + 1))).restrict C
  have hQ := quasiMeasurePreserving_native_inverse_positive_cone hS
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1)
  have hcoord : Measure.QuasiMeasurePreserving ξ σ μ :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).comp hQ
  have hfAS : AEStronglyMeasurable (fun y => f (ξ y)) σ :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving hcoord
  have hT : Measurable T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hFAS : AEStronglyMeasurable (fun y => κ (T y) • f (ξ y)) σ :=
    (hκ.comp hT).aestronglyMeasurable.smul hfAS
  have hFmeas : AEMeasurable (fun y => ENNReal.ofReal (‖κ (T y) • f (ξ y)‖ ^ 2)) σ :=
    (hFAS.norm.pow 2).aemeasurable.ennreal_ofReal
  have hJac := lintegral_native_positive_cone hS
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1) hFmeas
  have hTr (t : ℝ) (x : Domain n) : T (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) = t := by
    dsimp only [T]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
  have hξr (t : ℝ) (ht : t ≠ 0) (x : Domain n) :
      ξ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) = x := by
    dsimp only [ξ]
    rw [hTr, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hFaceInt : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.integrable_norm_pow (by decide)
  have hFaceOfReal : ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hFaceInt (Eventually.of_forall fun _ => sq_nonneg _)
  have hFaceFinite : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) ≠ ⊤ := by
    rw [← hFaceOfReal]
    exact ENNReal.ofReal_ne_top
  have hInner (t : ℝ) (ht : 0 < t) :
      (∫⁻ x in S, ENNReal.ofReal
        (‖κ (T (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) •
          f (ξ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)))‖ ^ 2)) =
        ENNReal.ofReal ((κ t) ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
    simp_rw [hTr, hξr t ht.ne', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ENNReal.ofReal_mul (sq_nonneg (κ t))]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hLInt : (∫⁻ y, ENNReal.ofReal (‖κ (T y) • f (ξ y)‖ ^ 2) ∂σ) =
      (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((κ t) ^ 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
    rw [hJac]
    calc
      _ = ∫⁻ t, (ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((κ t) ^ 2)) *
          (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [hInner t ht.1, mul_assoc]
      _ = _ := lintegral_mul_const' _ _ hFaceFinite
  have hFInt : Integrable (fun y => ‖κ (T y) • f (ξ y)‖ ^ 2) σ := by
    apply (lintegral_ofReal_ne_top_iff_integrable (hFAS.norm.pow 2)
      (Eventually.of_forall fun _ => sq_nonneg _)).mp
    change (∫⁻ y, ENNReal.ofReal (‖κ (T y) • f (ξ y)‖ ^ 2) ∂σ) ≠ ⊤
    rw [hLInt]
    exact ENNReal.mul_ne_top hMoment hFaceFinite
  refine ⟨(memLp_two_iff_integrable_sq_norm hFAS).mpr hFInt, ?_⟩
  have hConeOfReal := ofReal_integral_eq_lintegral_ofReal hFInt
    (Eventually.of_forall fun _ => sq_nonneg _)
  rw [← hConeOfReal, ← hFaceOfReal] at hLInt
  have hReal := congrArg ENNReal.toReal hLInt
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)] at hReal
  exact hReal

/-- Original face L2 data have the same literal degree-zero pullback in native
cone L2, with its exact 1/(n+1) quadratic integral. -/
theorem memLp_two_native_cone_pullback {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict S)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ S}
    MemLp (fun y => f (ξ y)) 2 (volume.restrict C) ∧
    (∫ y in C, ‖f (ξ y)‖ ^ 2) = ((n : ℝ) + 1)⁻¹ * ∫ x in S, ‖f x‖ ^ 2 := by
  intro e T ξ C
  have hMoment : (∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((1 : ℝ) ^ 2)) =
      ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
    simpa only [one_pow, ENNReal.ofReal_one, mul_one] using lintegral_unit_interval_nat_pow n
  obtain ⟨hL, hE⟩ := weighted_native_cone_l2 hS hf (fun _ => 1) measurable_const
    (by rw [hMoment]; exact ENNReal.ofReal_ne_top)
  refine ⟨by simpa only [one_smul] using hL, ?_⟩
  rw [hMoment, ENNReal.toReal_ofReal (by positivity)] at hE
  simpa only [one_smul] using hE

/-- In face dimension at least two, the original face L2 data with their
literal inverse-radius factor are native cone L2 with exact 1/(n-1) energy. -/
theorem memLp_two_native_cone_inverse_pullback {n : ℕ} (hn : 2 ≤ n) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict S)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ S}
    MemLp (fun y => (T y)⁻¹ • f (ξ y)) 2 (volume.restrict C) ∧
    (∫ y in C, ‖(T y)⁻¹ • f (ξ y)‖ ^ 2) =
      ((n : ℝ) - 1)⁻¹ * ∫ x in S, ‖f x‖ ^ 2 := by
  intro e T ξ C
  have hMoment := lintegral_unit_cone_inverse_square_moment hn
  obtain ⟨hL, hE⟩ := weighted_native_cone_l2 hS hf (fun t => t⁻¹) measurable_inv
    (by rw [hMoment]; exact ENNReal.ofReal_ne_top)
  refine ⟨hL, ?_⟩
  have hnreal : 0 < (n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [hMoment, ENNReal.toReal_ofReal (inv_nonneg.mpr hnreal.le)] at hE
  exact hE

end StratificationTheory
