module

public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate
public import StratificationTheory.Foundation.UnitSquareCoordinateSwap

public section

open HarmonicMaps

namespace StratificationTheory

/-- Every positive canonical coordinate exchange is its own inverse on the
entire original Euclidean carrier. -/
theorem cubical_positive_face_isometry_involutive {n : ℕ} (i : Fin (n + 1))
    (z : Domain (n + 1)) :
    cubicalSignedFaceIsometry n i true (cubicalSignedFaceIsometry n i true z) = z := by
  have hCoordinate (z₀ : Domain (n + 1)) (k : Fin (n + 1)) :
      cubicalSignedFaceIsometry n i true z₀ ((Equiv.swap (Fin.last n) i) k) = z₀ k := by
    rw [cubicalSignedFaceIsometry_apply]
    simp only [ite_true, ite_self]
  ext k
  have h := hCoordinate (cubicalSignedFaceIsometry n i true z) ((Equiv.swap (Fin.last n) i) k)
  rw [Equiv.swap_apply_self] at h
  exact h.trans (hCoordinate z k)

/-- The actual native coordinates of a spatial facet in four-dimensional
space-time retain the original two spatial coordinates and original time
of the corresponding three-dimensional prism. -/
theorem three_prism_spacetime_spatial_facet_coordinates (i : Fin 3) (positive : Bool)
    (z : Domain 3) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
    let A := cubicalSignedFaceIsometry 2 i true
    let spatial := cubicalSignedFaceIsometry 2 i positive
      (e.symm ((e z).1, EuclideanSpace.single (0 : Fin 1) 1))
    cubicalSignedFaceIsometry 3 i.castSucc positive
      (E.symm (A z, EuclideanSpace.single (0 : Fin 1) 1)) =
      WithLp.toLp 2 ![spatial 0, spatial 1, spatial 2, (e z).2 0] := by
  intro e E A spatial
  have hCap₃ (v : Domain 2) : e.symm (v, EuclideanSpace.single (0 : Fin 1) 1) =
      WithLp.toLp 2 ![v 0, v 1, (1 : ℝ)] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  have hCap₄ (v : Domain 3) : E.symm (v, EuclideanSpace.single (0 : Fin 1) 1) =
      WithLp.toLp 2 ![v 0, v 1, v 2, (1 : ℝ)] := by
    apply E.injective
    rw [E.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  have hBase₀ : (e z).1 0 = z 0 := rfl
  have hBase₁ : (e z).1 1 = z 1 := rfl
  have hTime : (e z).2 0 = z 2 := rfl
  rw [hCap₄]
  dsimp only [spatial]
  rw [hCap₃]
  cases positive <;> fin_cases i <;> ext k <;> fin_cases k <;>
    simp [A, cubicalSignedFaceIsometry_coordinate, Fin.last, Equiv.swap_apply_def, hBase₀, hBase₁, hTime]

end StratificationTheory
