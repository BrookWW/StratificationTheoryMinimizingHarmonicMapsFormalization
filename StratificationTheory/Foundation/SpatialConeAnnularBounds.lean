module

public import StratificationTheory.Foundation.SpatialConeTimeSobolev
public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

/-!
# Actual bounded positive-height carriers on a spatial annulus

The Euclidean annulus supplies a dimension-only lower cone height. The
independent time interval lies in (0,1), so the same actual spatial-time
points lie in one fixed Euclidean ball for the native Sobolev pullback.
-/

public section
open HarmonicMaps MeasureTheory Set Metric
open scoped BigOperators
namespace StratificationTheory

/-- The actual positive spatial annular cone with an independent open time
slab is an open Euclidean carrier. -/
theorem isOpen_positive_spatial_annular_cone (n : ℕ) (ε : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e (E y).1).2 0
    IsOpen (({y : Domain (n + 1 + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |(e (E y).1).1 i| < T y} ∩
      {y | ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1}) ∩ {y | (E y).2 0 ∈ Ioo (0 : ℝ) ε}) := by
  intro e E T
  have hT : Continuous T := by dsimp only [T]; fun_prop
  have hX (i : Fin n) : Continuous (fun y : Domain (n + 1 + 1) => |(e (E y).1).1 i|) := by
    fun_prop
  have hTime : Continuous (fun y : Domain (n + 1 + 1) => (E y).2 0) := by fun_prop
  have hCone : IsOpen {y : Domain (n + 1 + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |(e (E y).1).1 i| < T y} := by
    have hSet : {y : Domain (n + 1 + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧
        ∀ i : Fin n, |(e (E y).1).1 i| < T y} =
        (T ⁻¹' Ioo (0 : ℝ) 1) ∩ ⋂ i : Fin n, {y | |(e (E y).1).1 i| < T y} := by
      ext y
      simp only [mem_setOf_eq,mem_inter_iff,mem_preimage,mem_iInter]
    rw [hSet]
    exact (isOpen_Ioo.preimage hT).inter
      (isOpen_iInter_of_finite fun i : Fin n => isOpen_lt (hX i) hT)
  exact (hCone.inter (isOpen_Ioo.preimage (continuous_fst.comp E.continuous).norm)).inter
    (isOpen_Ioo.preimage hTime)

theorem norm_euclidean_le_card_mul_coordinate_bound {n : ℕ}
    (x : Domain n) (M : ℝ) (hx : ∀ i : Fin n, |x i| ≤ M) :
    ‖x‖ ≤ (n : ℝ) * M := by
  have hRep : (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) = x := by
    ext k
    simp [Pi.single_apply]
  calc
    ‖x‖ = ‖∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)‖ := by rw [hRep]
    _ ≤ ∑ i : Fin n, ‖x i • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      have he : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
        simpa only [norm_one] using PiLp.norm_single 2 (fun _ : Fin n => ℝ) i (1 : ℝ)
      rw [he,mul_one]
      exact hx i
    _ = (n : ℝ) * M := by simp

/-- Every actual positive cone point in the fixed spatial annulus and
original time slab belongs to the genuine bounded pullback carrier. -/
theorem spatial_cone_annular_transport_carrier {n : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    (y : Domain (n + 1 + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T := (e (E y).1).2 0
    let ρ : ℝ := (4 * ((n + 1 : ℕ) : ℝ))⁻¹
    let F := e.symm (T⁻¹ • (e (E y).1).1,(E y).2)
    0 < T → (∀ i : Fin n, |(e (E y).1).1 i| < T) →
    ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1 → (E y).2 0 ∈ Ioo (0 : ℝ) ε →
    T ∈ Ioo ρ 2 ∧
      (e F).1 ∈ ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1 ∧
      (e F).2 0 ∈ Ioo (0 : ℝ) ε ∧ ‖y‖ < 2 := by
  intro e E T ρ F hT hStrict hAnn hTime
  have hAll : ∀ i : Fin (n + 1), |(E y).1 i| ≤ T := by
    intro i
    refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin 1 => ?_) i
    · exact (hStrict j).le
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change |T| ≤ T
      rw [abs_of_pos hT]
  have hNorm := norm_euclidean_le_card_mul_coordinate_bound (E y).1 T hAll
  have hDim : 0 < 4 * ((n + 1 : ℕ) : ℝ) := by positivity
  have hLow : ρ < T := by
    change (4 * ((n + 1 : ℕ) : ℝ))⁻¹ < T
    rw [← one_div]
    apply (div_lt_iff₀ hDim).mpr
    nlinarith only [hNorm,hAnn.1]
  have hTNorm : T ≤ ‖(E y).1‖ := by
    have h := PiLp.norm_apply_le (E y).1 (Fin.natAdd n (0 : Fin 1))
    change ‖T‖ ≤ ‖(E y).1‖ at h
    simpa only [Real.norm_eq_abs,abs_of_pos hT] using h
  have hTTwo : T < 2 := lt_trans (hTNorm.trans_lt hAnn.2) (by norm_num)
  have hBase : (e F).1 ∈ ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1 := by
    change (e (e.symm (T⁻¹ • (e (E y).1).1,(E y).2))).1 ∈ _
    rw [e.apply_symm_apply]
    exact (inverse_smul_mem_unit_coordinate_face_iff hT (e (E y).1).1).mpr hStrict
  have hFT : (e F).2 0 ∈ Ioo (0 : ℝ) ε := by
    change (e (e.symm (T⁻¹ • (e (E y).1).1,(E y).2))).2 0 ∈ _
    rwa [e.apply_symm_apply]
  have hNormSq : ‖y‖ ^ 2 = ‖(E y).1‖ ^ 2 + ((E y).2 0) ^ 2 := by
    have hTimeSq : ‖(E y).2‖ ^ 2 = ((E y).2 0) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one]
    have h := norm_sq_finAddEquivProd_symm (E y)
    change ‖E.symm (E y)‖ ^ 2 = _ at h
    rw [E.symm_apply_apply] at h
    rw [hTimeSq] at h
    exact h
  have hTimeOne : (E y).2 0 < 1 := hTime.2.trans_le hε
  have hY : ‖y‖ < 2 := by
    nlinarith only [hNormSq,hAnn.2,hTime.1,hTimeOne,norm_nonneg (E y).1,norm_nonneg y]
  exact ⟨⟨hLow,hTTwo⟩,hBase,hFT,hY⟩

end StratificationTheory
