module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import StratificationTheory.Foundation.CubicalConeMoments

/-!
# Literal unit-face geometry and native volume

The open coordinate face has native volume 2^n. A positive inverse dilation
identifies its membership with the physical strict cone inequalities. Their
native cone volume is exactly 2^n/(n+1).
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- Membership in the literal open unit face is exactly the strict
maximum-coordinate bound, with the original Euclidean coordinate values. -/
theorem mem_unit_coordinate_face_iff {n : ℕ} (x : Domain n) :
    x ∈ (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) ↔
      ∀ i : Fin n, |x i| < 1 := by
  simp only [mem_iInter, mem_preimage, mem_Ioo, abs_lt]
  rfl

/-- Positive inverse dilation gives the actual physical face-cone
inequalities, without replacing a norm or an original coordinate witness. -/
theorem inverse_smul_mem_unit_coordinate_face_iff {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : Domain n) :
    t⁻¹ • x ∈ (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) ↔
      ∀ i : Fin n, |x i| < t := by
  rw [mem_unit_coordinate_face_iff]
  apply forall_congr'
  intro i
  rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr ht)]
  have hEq : t⁻¹ * |x i| = |x i| / t := by rw [div_eq_mul_inv, mul_comm]
  rw [hEq]
  exact div_lt_one ht

/-- The unit face carries its actual Euclidean volume 2^n, including the
zero-dimensional face convention. -/
theorem volume_unit_coordinate_face (n : ℕ) :
    (volume : Measure (Domain n))
      (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) = (2 : ℝ≥0∞) ^ n := by
  let S : Set (Fin n → ℝ) := Set.pi univ (fun _ => Ioo (-1 : ℝ) 1)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have hm := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hS.nullMeasurableSet
  have hpre : (WithLp.ofLp : Domain n → (Fin n → ℝ)) ⁻¹' S =
      ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext x
    simp only [S, mem_preimage, mem_pi, mem_univ, forall_const, mem_iInter]
    rfl
  rw [hpre] at hm
  rw [hm]
  change (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) S = _
  simp [S, Measure.pi_pi, Real.volume_Ioo]
  norm_num

/-- The actual native unit face is a finite-measure domain. -/
theorem volume_unit_coordinate_face_ne_top (n : ℕ) :
    (volume : Measure (Domain n))
      (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) ≠ ⊤ := by
  rw [volume_unit_coordinate_face]
  exact ENNReal.pow_ne_top (by norm_num)

/-- The actual Euclidean positive unit face cone has exact native volume,
obtained from the native Jacobian and its scalar unit-interval moment. -/
theorem volume_native_unit_face_cone (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (volume : Measure (Domain (n + 1)))
      {y | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧ ∀ i : Fin n, |(e y).1 i| < (e y).2 0} =
        ENNReal.ofReal (((n : ℝ) + 1)⁻¹) * (2 : ℝ≥0∞) ^ n := by
  intro e
  let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
  have hS : MeasurableSet S := MeasurableSet.iInter (fun i : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable)
  have hC : {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
        ∀ i : Fin n, |(e y).1 i| < (e y).2 0} =
      {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
        ((e y).2 0)⁻¹ • (e y).1 ∈ S} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (e y).1).mpr hy.2⟩
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (e y).1).mp hy.2⟩
  rw [hC]
  have hJac := lintegral_native_positive_cone hS
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1)
    (f := fun _ : Domain (n + 1) => (1 : ℝ≥0∞)) measurable_const.aemeasurable
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul] at hJac
  have hvol : (volume : Measure (Domain n)) S = (2 : ℝ≥0∞) ^ n := volume_unit_coordinate_face n
  rw [hvol] at hJac
  rw [hJac, lintegral_mul_const' ((2 : ℝ≥0∞) ^ n) _ (ENNReal.pow_ne_top (by norm_num)),
    lintegral_unit_interval_nat_pow]

/-- The physical cone has finite native volume arbitrarily near its vertex. -/
theorem volume_native_unit_face_cone_ne_top (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (volume : Measure (Domain (n + 1)))
      {y | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧ ∀ i : Fin n, |(e y).1 i| < (e y).2 0} ≠ ⊤ := by
  intro e
  rw [volume_native_unit_face_cone]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (by norm_num))

/-- The actual native cone is non-null in every face dimension. -/
theorem volume_native_unit_face_cone_pos (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    0 < (volume : Measure (Domain (n + 1)))
      {y | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧ ∀ i : Fin n, |(e y).1 i| < (e y).2 0} := by
  intro e
  rw [volume_native_unit_face_cone]
  apply ENNReal.mul_pos
  · exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (by positivity))).ne'
  · exact pow_ne_zero n (by norm_num)

end StratificationTheory
