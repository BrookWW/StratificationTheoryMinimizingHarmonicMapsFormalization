module

public import StratificationTheory.Foundation.TranslatedCubeAffineCoordinates
public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps

namespace StratificationTheory

/-- The same actual inverse cube similarity splits in every positive
physical coordinate-normal chart into its original transverse inverse
similarity and original affine normal parameter. -/
theorem inverse_translated_cube_face_coordinates {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (lo : Domain (n + 1)) (i : Fin (n + 1)) (x : Domain n) (t : ℝ) :
    let Q := cubicalSignedFaceIsometry n i true
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let l : Domain n := WithLp.toLp 2 (fun k => lo ((Equiv.swap (Fin.last n) i) k.castSucc))
    let a : Domain (n + 1) := lo + WithLp.toLp 2 (fun _ => ε / 2)
    let b : Domain n := l + WithLp.toLp 2 (fun _ => ε / 2)
    (ε / 2)⁻¹ • (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) - a) =
      Q (e.symm ((ε / 2)⁻¹ • (x - b),
        EuclideanSpace.single (0 : Fin 1) ((t - lo i) / (ε / 2) - 1))) := by
  intro Q e l a b
  have hCenter : e (Q.symm a) = (b, EuclideanSpace.single (0 : Fin 1) (lo i + ε / 2)) := by
    apply Prod.ext
    · ext k
      change Q.symm a k.castSucc = b k
      rw [cubicalSignedFaceIsometry_symm_apply, if_neg (Fin.castSucc_ne_last k)]
      rfl
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      change Q.symm a (Fin.last n) = lo i + ε / 2
      rw [cubicalSignedFaceIsometry_symm_apply, if_pos rfl, if_pos rfl]
      rfl
  have hNative : (ε / 2)⁻¹ • (e.symm (x, EuclideanSpace.single (0 : Fin 1) t) - Q.symm a) =
      e.symm ((ε / 2)⁻¹ • (x - b), EuclideanSpace.single (0 : Fin 1) ((t - lo i) / (ε / 2) - 1)) := by
    apply e.injective
    rw [e.map_smul, e.map_sub, e.apply_symm_apply, hCenter, e.apply_symm_apply]
    apply Prod.ext
    · rfl
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      change (ε / 2)⁻¹ * (t - (lo i + ε / 2)) = (t - lo i) / (ε / 2) - 1
      field_simp
      ring
  calc
    _ = Q ((ε / 2)⁻¹ • (e.symm (x, EuclideanSpace.single (0 : Fin 1) t) - Q.symm a)) := by
      rw [Q.map_smul, Q.map_sub, Q.apply_symm_apply]
    _ = _ := congrArg Q hNative

end StratificationTheory
