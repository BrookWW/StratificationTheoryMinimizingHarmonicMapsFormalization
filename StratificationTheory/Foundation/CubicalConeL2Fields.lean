module

public import StratificationTheory.Foundation.CubicalConeL2
public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.CubicalConeGradientBound

/-!
# Native quadratic data of the literal face-cone fields

The original face function and column L2 data give finite native L2 fields
on the unit cone. Their same displayed columns have exact quadratic integrals
and the dimension-dependent HS bound.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- Original function and column L2 data produce the literal cone function
and column fields with their exact native quadratic integrals. -/
theorem native_unit_face_cone_l2_energy_data {n q : ℕ} (hn : 2 ≤ n)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemLp w 2 (volume.restrict
      (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1)))
    (hDw : ∀ i, MemLp (fun x => Dw x i) 2 (volume.restrict
      (⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1))) :
    let B := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ∀ i : Fin n, |(e y).1 i| < T y}
    let W : Domain (n + 1) → Ambient q := fun y => w (ξ y)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun i : Fin n => (T y)⁻¹ • Dw (ξ y) i)
        (fun _last : Fin 1 => -((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (ξ y) i))
    MemLp W 2 (volume.restrict C) ∧
    (∀ i, MemLp (fun y => D y i) 2 (volume.restrict C)) ∧
    Integrable (fun y => ‖W y‖ ^ 2) (volume.restrict C) ∧
    (∫ y in C, ‖W y‖ ^ 2) = ((n : ℝ) + 1)⁻¹ * ∫ x in B, ‖w x‖ ^ 2 ∧
    Integrable (fun y => hsNormSq (D y)) (volume.restrict C) ∧
    (∫ y in C, hsNormSq (D y)) =
      ((n : ℝ) - 1)⁻¹ * ∫ x in B,
        hsNormSq (Dw x) + ‖∑ i : Fin n, x i • Dw x i‖ ^ 2 ∧
    (∫ y in C, hsNormSq (D y)) ≤
      (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B, hsNormSq (Dw x) := by
  intro B e T ξ C W D
  have hB : MeasurableSet B := MeasurableSet.iInter (fun i : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable)
  have hCeq : C = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (e y).1).mpr hy.2⟩
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (e y).1).mp hy.2⟩
  have hWdata : MemLp W 2 (volume.restrict C) ∧
      (∫ y in C, ‖W y‖ ^ 2) = ((n : ℝ) + 1)⁻¹ * ∫ x in B, ‖w x‖ ^ 2 := by
    rw [hCeq]
    exact memLp_two_native_cone_pullback hB hw
  let V : Domain n → Ambient q := fun x => ∑ i : Fin n, x i • Dw x i
  have hcoef (i : Fin n) : MemLp (fun x : Domain n => x i) ∞ (volume.restrict B) := by
    apply memLp_top_of_bound
      (f := fun x : Domain n => x i) (EuclideanSpace.proj i).continuous.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem hB] with x hx
    exact (mem_unit_coordinate_face_iff x).mp hx i |>.le
  have hV : MemLp V 2 (volume.restrict B) := by
    simpa only [V, Finset.sum_apply, Pi.smul_apply'] using memLp_finsetSum Finset.univ
      (fun i _ => (hDw i).smul (r := (2 : ℝ≥0∞)) (hcoef i))
  have hSpatial (i : Fin n) :
      MemLp (fun y => (T y)⁻¹ • Dw (ξ y) i) 2 (volume.restrict C) ∧
      (∫ y in C, ‖(T y)⁻¹ • Dw (ξ y) i‖ ^ 2) =
        ((n : ℝ) - 1)⁻¹ * ∫ x in B, ‖Dw x i‖ ^ 2 := by
    rw [hCeq]
    exact memLp_two_native_cone_inverse_pullback hn hB (hDw i)
  have hTime : MemLp (fun y => (T y)⁻¹ • V (ξ y)) 2 (volume.restrict C) ∧
      (∫ y in C, ‖(T y)⁻¹ • V (ξ y)‖ ^ 2) =
        ((n : ℝ) - 1)⁻¹ * ∫ x in B, ‖V x‖ ^ 2 := by
    rw [hCeq]
    exact memLp_two_native_cone_inverse_pullback hn hB hV
  have hD (i : Fin (n + 1)) : MemLp (fun y => D y i) 2 (volume.restrict C) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [D, Fin.addCases_left] using (hSpatial j).1
    · simp only [D, Fin.addCases_right]
      exact hTime.1.neg
  have hHSI := integrable_hsNormSq_of_memLp_columns hD
  have hBI := integrable_hsNormSq_of_memLp_columns hDw
  have hVI := hV.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hSI (i : Fin n) := (hSpatial i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hTI := hTime.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hSsumI : Integrable (fun y => ∑ i : Fin n, ‖(T y)⁻¹ • Dw (ξ y) i‖ ^ 2)
      (volume.restrict C) := integrable_finsetSum Finset.univ (fun i _ => hSI i)
  have hsplit (y : Domain (n + 1)) : hsNormSq (D y) =
      (∑ i : Fin n, ‖(T y)⁻¹ • Dw (ξ y) i‖ ^ 2) + ‖(T y)⁻¹ • V (ξ y)‖ ^ 2 := by
    rw [hsNormSq, Fin.sum_univ_add (a := n) (b := 1)]
    simp only [D, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one, norm_neg]
    rfl
  have hBaseSum : (∫ x in B, hsNormSq (Dw x)) =
      ∑ i : Fin n, ∫ x in B, ‖Dw x i‖ ^ 2 := by
    exact integral_finsetSum Finset.univ (fun i _ => (hDw i).integrable_norm_pow (by decide))
  have hEnergy : (∫ y in C, hsNormSq (D y)) =
      ((n : ℝ) - 1)⁻¹ * ∫ x in B, hsNormSq (Dw x) + ‖V x‖ ^ 2 := by
    calc
      _ = ∫ y in C, (∑ i : Fin n, ‖(T y)⁻¹ • Dw (ξ y) i‖ ^ 2) + ‖(T y)⁻¹ • V (ξ y)‖ ^ 2 :=
        integral_congr_ae (Eventually.of_forall hsplit)
      _ = (∑ i : Fin n, ∫ y in C, ‖(T y)⁻¹ • Dw (ξ y) i‖ ^ 2) +
          ∫ y in C, ‖(T y)⁻¹ • V (ξ y)‖ ^ 2 := by
        rw [integral_add hSsumI hTI, integral_finsetSum Finset.univ (fun i _ => hSI i)]
      _ = (∑ i : Fin n, ((n : ℝ) - 1)⁻¹ * ∫ x in B, ‖Dw x i‖ ^ 2) +
          ((n : ℝ) - 1)⁻¹ * ∫ x in B, ‖V x‖ ^ 2 := by
        rw [hTime.2]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => (hSpatial i).2)
      _ = _ := by rw [← Finset.mul_sum, integral_add hBI hVI, hBaseSum]; ring
  have hVbound : ∀ᵐ x ∂volume.restrict B, ‖V x‖ ^ 2 ≤ (n : ℝ) * hsNormSq (Dw x) := by
    filter_upwards [ae_restrict_mem hB] with x hx
    exact norm_sum_smul_sq_le_dimension_energy (fun i => x i) (Dw x)
      (fun i => ((mem_unit_coordinate_face_iff x).mp hx i).le)
  have hVint := integral_mono_ae hVI (hBI.const_mul (n : ℝ)) hVbound
  rw [integral_const_mul] at hVint
  have hBound : (∫ y in C, hsNormSq (D y)) ≤
      (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B, hsNormSq (Dw x) := by
    rw [hEnergy, integral_add hBI hVI]
    have hnreal : 0 < (n : ℝ) - 1 := by
      have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hsum : (∫ x in B, hsNormSq (Dw x)) + (∫ x in B, ‖V x‖ ^ 2) ≤
        ((n : ℝ) + 1) * ∫ x in B, hsNormSq (Dw x) := by linarith only [hVint]
    exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnreal.le)).trans_eq (by ring)
  exact ⟨hWdata.1, hD, hWdata.1.integrable_norm_pow (by decide), hWdata.2, hHSI, hEnergy, hBound⟩

end StratificationTheory
