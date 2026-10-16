module

public import StratificationTheory.Foundation.ConicalSideGeometry

/-!
# Euclidean normal coordinates of a conical lateral plane

The spatial last coordinate and height undergo the oriented forty-five degree
rotation. Positive normal coordinates point into the cone through `T - L > 0`.
All coordinate formulas concern one actual Euclidean linear isometry.
-/

public section
open HarmonicMaps MeasureTheory Set
namespace StratificationTheory

private theorem norm_sq_domainOne (z : Domain 1) : ‖z‖ ^ 2 = (z 0) ^ 2 := by
  have h := isometry_domainOne_eval.dist_eq z (0 : Domain 1)
  simp only [dist_eq_norm, sub_zero, PiLp.zero_apply, Real.norm_eq_abs] at h
  rw [← h, sq_abs]

private theorem exists_native_cone_normal_isometry (n : ℕ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    ∃ Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ y, e (Q y) =
        (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
          (((b (e y).1).2 0 - (e y).2 0) / Real.sqrt 2)),
         EuclideanSpace.single (0 : Fin 1) (((b (e y).1).2 0 + (e y).2 0) / Real.sqrt 2))) ∧
      (∀ y, e (Q.symm y) =
        (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
          (((b (e y).1).2 0 + (e y).2 0) / Real.sqrt 2)),
         EuclideanSpace.single (0 : Fin 1) (((e y).2 0 - (b (e y).1).2 0) / Real.sqrt 2))) := by
  intro b e
  let d : ℝ := Real.sqrt 2
  have hd2 : d ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let F : Domain ((n + 1) + 1) → Domain ((n + 1) + 1) := fun y =>
    e.symm (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
      (((b (e y).1).2 0 - (e y).2 0) / d)),
      EuclideanSpace.single (0 : Fin 1) (((b (e y).1).2 0 + (e y).2 0) / d))
  let G : Domain ((n + 1) + 1) → Domain ((n + 1) + 1) := fun y =>
    e.symm (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
      (((b (e y).1).2 0 + (e y).2 0) / d)),
      EuclideanSpace.single (0 : Fin 1) (((e y).2 0 - (b (e y).1).2 0) / d))
  have hsingle (z : Domain 1) : EuclideanSpace.single (0 : Fin 1) (z 0) = z := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply, ite_true]
  have hGF (y : Domain ((n + 1) + 1)) : G (F y) = y := by
    apply e.injective
    simp only [G, F, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
    apply Prod.ext
    · apply b.injective
      rw [b.apply_symm_apply]
      apply Prod.ext
      · rfl
      · have h : (((b (e y).1).2 0 - (e y).2 0) / d +
            ((b (e y).1).2 0 + (e y).2 0) / d) / d = (b (e y).1).2 0 := by
          rw [← add_div, div_div, ← pow_two, hd2]
          ring
        rw [h, hsingle]
    · have h : (((b (e y).1).2 0 + (e y).2 0) / d -
          ((b (e y).1).2 0 - (e y).2 0) / d) / d = (e y).2 0 := by
        rw [← sub_div, div_div, ← pow_two, hd2]
        ring
      rw [h, hsingle]
  have hFG (y : Domain ((n + 1) + 1)) : F (G y) = y := by
    apply e.injective
    simp only [G, F, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
    apply Prod.ext
    · apply b.injective
      rw [b.apply_symm_apply]
      apply Prod.ext
      · rfl
      · have h : (((b (e y).1).2 0 + (e y).2 0) / d -
            ((e y).2 0 - (b (e y).1).2 0) / d) / d = (b (e y).1).2 0 := by
          rw [← sub_div, div_div, ← pow_two, hd2]
          ring
        rw [h, hsingle]
    · have h : (((b (e y).1).2 0 + (e y).2 0) / d +
          ((e y).2 0 - (b (e y).1).2 0) / d) / d = (e y).2 0 := by
        rw [← add_div, div_div, ← pow_two, hd2]
        ring
      rw [h, hsingle]
  have hAdd (x y : Domain ((n + 1) + 1)) : F (x + y) = F x + F y := by
    apply e.injective
    simp only [F, map_add, e.apply_symm_apply, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
    apply Prod.ext
    · simp only [Prod.fst_add]
      rw [← b.symm.map_add]
      congr 1
      apply Prod.ext
      · rfl
      · simp only [Prod.snd_add]
        rw [← PiLp.single_add]
        congr 1
        ring
    · simp only [Prod.snd_add]
      rw [← PiLp.single_add]
      congr 1
      ring
  have hSmul (r : ℝ) (y : Domain ((n + 1) + 1)) : F (r • y) = r • F y := by
    apply e.injective
    simp only [F, map_smul, e.apply_symm_apply, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
    apply Prod.ext
    · simp only [Prod.smul_fst]
      rw [← b.symm.map_smul]
      congr 1
      apply Prod.ext
      · rfl
      · simp only [Prod.smul_snd]
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [PiLp.single_apply, ite_true, PiLp.smul_apply, smul_eq_mul]
        ring
    · simp only [Prod.smul_snd]
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.single_apply, ite_true, PiLp.smul_apply, smul_eq_mul]
      ring
  let L : Domain ((n + 1) + 1) ≃ₗ[ℝ] Domain ((n + 1) + 1) :=
    { toFun := F, invFun := G, left_inv := hGF, right_inv := hFG,
      map_add' := hAdd, map_smul' := hSmul }
  have hNorm (y : Domain ((n + 1) + 1)) : ‖L y‖ = ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hSource : ‖y‖ ^ 2 = ‖(b (e y).1).1‖ ^ 2 + ((b (e y).1).2 0) ^ 2 + ((e y).2 0) ^ 2 := by
      have he := norm_sq_finAddEquivProd_symm (e y)
      have hb := norm_sq_finAddEquivProd_symm (b (e y).1)
      rw [e.symm_apply_apply] at he
      rw [b.symm_apply_apply] at hb
      rw [hb, norm_sq_domainOne, norm_sq_domainOne] at he
      exact he
    change ‖F y‖ ^ 2 = _
    dsimp only [F]
    rw [norm_sq_finAddEquivProd_symm, norm_sq_finAddEquivProd_symm,
      PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hSource,
      div_pow, div_pow, hd2]
    ring
  let Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1) := { L with norm_map' := hNorm }
  refine ⟨Q, ?_, ?_⟩
  · intro y
    exact e.apply_symm_apply _
  · intro y
    exact e.apply_symm_apply _

/-- One uniquely determined full Euclidean linear isometry gives the oriented
normal coordinates, their inverse, and the literal parallel-side formulas. -/
theorem exists_unique_native_cone_normal_coordinates (n : ℕ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    ∃! Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ y, e (Q y) =
        (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
          (((b (e y).1).2 0 - (e y).2 0) / Real.sqrt 2)),
         EuclideanSpace.single (0 : Fin 1) (((b (e y).1).2 0 + (e y).2 0) / Real.sqrt 2))) ∧
      (∀ y, e (Q.symm y) =
        (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
          (((b (e y).1).2 0 + (e y).2 0) / Real.sqrt 2)),
         EuclideanSpace.single (0 : Fin 1) (((e y).2 0 - (b (e y).1).2 0) / Real.sqrt 2))) ∧
      (∀ z, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) 0)) =
        e.symm (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)),
          EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2))) ∧
      (∀ z η,
        let y := Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))
        (b (e y).1).1 = (b z).1 ∧
        (b (e y).1).2 0 = ((b z).2 0 - η) / Real.sqrt 2 ∧
        (e y).2 0 = ((b z).2 0 + η) / Real.sqrt 2 ∧
        (e y).2 0 - (b (e y).1).2 0 = Real.sqrt 2 * η) ∧
      (∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) =
        e.symm (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1)
          (((b z).2 0 + η) / Real.sqrt 2 - Real.sqrt 2 * η)),
          EuclideanSpace.single (0 : Fin 1) (((b z).2 0 + η) / Real.sqrt 2))) ∧
      (∀ z η,
        let z' := b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 + η))
        Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) =
          e.symm (b.symm ((b z').1, EuclideanSpace.single (0 : Fin 1)
            ((b z').2 0 / Real.sqrt 2 - Real.sqrt 2 * η)),
            EuclideanSpace.single (0 : Fin 1) ((b z').2 0 / Real.sqrt 2))) ∧
      (∀ z η, 0 < η →
        (b (e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)))).1).2 0 <
          (e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)))).2 0) := by
  intro b e
  obtain ⟨Q, hF, hI⟩ := exists_native_cone_normal_isometry n
  change (∀ y, e (Q y) =
    (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
      (((b (e y).1).2 0 - (e y).2 0) / Real.sqrt 2)),
      EuclideanSpace.single (0 : Fin 1) (((b (e y).1).2 0 + (e y).2 0) / Real.sqrt 2))) at hF
  have hdpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hd2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hTwoDiv : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 :=
    (div_eq_iff hdpos.ne').mpr (by nlinarith only [hd2])
  have hGap (s η : ℝ) : (s + η) / Real.sqrt 2 - (s - η) / Real.sqrt 2 = Real.sqrt 2 * η := by
    calc
      _ = (2 / Real.sqrt 2) * η := by ring
      _ = _ := by rw [hTwoDiv]
  have hSlice (z : Domain (n + 1)) (η : ℝ) :
      e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))) =
        (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) (((b z).2 0 - η) / Real.sqrt 2)),
          EuclideanSpace.single (0 : Fin 1) (((b z).2 0 + η) / Real.sqrt 2)) := by
    simpa only [e.apply_symm_apply, PiLp.single_apply, ite_true] using
      hF (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))
  have hParallel (z : Domain (n + 1)) (η : ℝ) :
      Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) =
        e.symm (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1)
          (((b z).2 0 + η) / Real.sqrt 2 - Real.sqrt 2 * η)),
          EuclideanSpace.single (0 : Fin 1) (((b z).2 0 + η) / Real.sqrt 2)) := by
    apply e.injective
    rw [hSlice, e.apply_symm_apply]
    apply Prod.ext
    · apply congrArg b.symm
      apply Prod.ext
      · rfl
      · apply congrArg (EuclideanSpace.single (0 : Fin 1))
        linarith only [hGap ((b z).2 0) η]
    · rfl
  refine ⟨Q, ⟨hF, hI, ?_, ?_, hParallel, ?_, ?_⟩, ?_⟩
  · intro z
    apply e.injective
    rw [hSlice, e.apply_symm_apply]
    simp only [sub_zero, add_zero]
  · intro z η y
    simp only [y, hSlice, b.apply_symm_apply, PiLp.single_apply, ite_true]
    simpa only [true_and] using hGap ((b z).2 0) η
  · intro z η z'
    dsimp only [z']
    rw [b.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
    exact hParallel z η
  · intro z η hη
    have h := hGap ((b z).2 0) η
    simp only [hSlice, b.apply_symm_apply, PiLp.single_apply, ite_true]
    linarith only [h, mul_pos hdpos hη]
  · intro Q' hQ'
    apply LinearIsometryEquiv.ext
    intro y
    apply e.injective
    exact (hQ'.1 y).trans (hF y).symm

end StratificationTheory
