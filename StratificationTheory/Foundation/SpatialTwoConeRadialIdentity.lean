module

public import StratificationTheory.Foundation.CubicalConeRadialFormula
public import StratificationTheory.Foundation.CubicalAdjacentConeSwap

/-!
# Actual two-cone radial values with independent time

Weak dominance already fixes the maximum-coordinate radial cap, including
the common lateral plane. The two original positive spatial face formulas
therefore agree with the same physical radial map across that plane.
-/

public section
open HarmonicMaps
namespace StratificationTheory

theorem positive_cube_cone_radial_retraction_le {n : ℕ} (y : Domain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T := (e y).2 0
    0 < T → (∀ i : Fin n, |(e y).1 i| ≤ T) →
    ‖WithLp.ofLp y‖⁻¹ • y = e.symm (T⁻¹ • (e y).1,EuclideanSpace.single (0 : Fin 1) 1) := by
  intro e T hT hOther
  have hLast : y (Fin.last n) = T := rfl
  have hNorm : ‖WithLp.ofLp y‖ = T := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hT.le).mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hLast,Real.norm_of_nonneg hT.le]
      · exact hOther j
    · have h := norm_le_pi_norm (WithLp.ofLp y) (Fin.last n)
      simpa only [hLast,Real.norm_of_nonneg hT.le] using h
  rw [hNorm]
  apply e.injective
  rw [e.map_smul,e.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change T⁻¹ * T = (EuclideanSpace.single (0 : Fin 1) 1) 0
    rw [inv_mul_cancel₀ hT.ne']
    rfl

theorem spatial_two_cone_radial_identity {n q : ℕ}
    (G : Domain (n + 1 + 1) × ℝ → Ambient q) (z : Domain (n + 1 + 1 + 1)) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let A := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    let R := fun y : Domain (n + 1 + 1 + 1) => E.symm (A (E y).1,(E y).2)
    let T := fun y : Domain (n + 1 + 1 + 1) => (e (E y).1).2 0
    let F := fun y : Domain (n + 1 + 1 + 1) => e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2)
    let w₀ := fun x : Domain (n + 1 + 1) => G
      (A (e.symm ((e x).1,EuclideanSpace.single (0 : Fin 1) 1)),(e x).2 0)
    let w₁ := fun x : Domain (n + 1 + 1) => G
      (e.symm ((e x).1,EuclideanSpace.single (0 : Fin 1) 1),(e x).2 0)
    0 < T z → 0 < (b (e (E z).1).1).2 0 →
    (∀ i : Fin n, |(b (e (E z).1).1).1 i| < min (T z) ((b (e (E z).1).1).2 0)) →
    (if T z < (b (e (E z).1).1).2 0 then w₀ (F (R z)) else w₁ (F z)) =
      G (‖WithLp.ofLp (E z).1‖⁻¹ • (E z).1,(E z).2 0) := by
  intro b e E A R T F w₀ w₁ hT hAdj hTang
  have hSwap (x : Domain (n + 1 + 1)) : e (A x) =
      (b.symm ((b (e x).1).1,EuclideanSpace.single (0 : Fin 1) ((e x).2 0)),
        EuclideanSpace.single (0 : Fin 1) ((b (e x).1).2 0)) :=
    (cubical_adjacent_cone_swap_coordinates n).1 x
  have hAA (x : Domain (n + 1 + 1)) : A (A x) = x :=
    (cubical_adjacent_cone_swap_coordinates n).2.1 x
  have hMax (x : Domain (n + 1 + 1)) : ‖WithLp.ofLp (A x)‖ = ‖WithLp.ofLp x‖ :=
    cubicalSignedFaceIsometry_coordinate_norm (Fin.last n).castSucc true x
  have hCap₀ (y : Domain (n + 1 + 1 + 1)) : w₀ (F y) = G
      (A (e.symm ((T y)⁻¹ • (e (E y).1).1,EuclideanSpace.single (0 : Fin 1) 1)),(E y).2 0) := by
    change G (A (e.symm ((e (e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2))).1,
      EuclideanSpace.single (0 : Fin 1) 1)),(e (e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2))).2 0) = _
    rw [e.apply_symm_apply]
  have hCap₁ (y : Domain (n + 1 + 1 + 1)) : w₁ (F y) = G
      (e.symm ((T y)⁻¹ • (e (E y).1).1,EuclideanSpace.single (0 : Fin 1) 1),(E y).2 0) := by
    change G (e.symm ((e (e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2))).1,
      EuclideanSpace.single (0 : Fin 1) 1),(e (e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2))).2 0) = _
    rw [e.apply_symm_apply]
  by_cases hCase : T z < (b (e (E z).1).1).2 0
  · rw [if_pos hCase,hCap₀]
    have hPos : 0 < (e (A (E z).1)).2 0 := by
      rw [hSwap]
      simpa only [PiLp.single_apply,ite_true] using hAdj
    have hOther : ∀ i : Fin (n + 1), |(e (A (E z).1)).1 i| ≤ (e (A (E z).1)).2 0 := by
      intro i
      refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin 1 => ?_) i
      · change |(b (e (A (E z).1)).1).1 j| ≤ (e (A (E z).1)).2 0
        rw [hSwap]
        simpa only [b.apply_symm_apply,PiLp.single_apply,ite_true] using
          (hTang j).le.trans (min_le_right _ _)
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change |(b (e (A (E z).1)).1).2 0| ≤ (e (A (E z).1)).2 0
        rw [hSwap]
        simp only [b.apply_symm_apply,PiLp.single_apply,ite_true]
        change |T z| ≤ (b (e (E z).1).1).2 0
        rw [abs_of_pos hT]
        exact hCase.le
    have hRad := positive_cube_cone_radial_retraction_le (A (E z).1) hPos hOther
    have hER : E (R z) = (A (E z).1,(E z).2) := E.apply_symm_apply _
    have hTR : T (R z) = (e (A (E z).1)).2 0 := by
      change (e (E (R z)).1).2 0 = _
      rw [hER]
    rw [hTR,hER]
    rw [← hRad,← cubical_radial_retraction_isometry A hMax,hAA]
  · rw [if_neg hCase,hCap₁]
    have hOther : ∀ i : Fin (n + 1), |(e (E z).1).1 i| ≤ T z := by
      intro i
      refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin 1 => ?_) i
      · exact (hTang j).le.trans (min_le_left _ _)
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change |(b (e (E z).1).1).2 0| ≤ T z
        rw [abs_of_pos hAdj]
        exact le_of_not_gt hCase
    rw [← positive_cube_cone_radial_retraction_le (E z).1 hT hOther]

end StratificationTheory
