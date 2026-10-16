module

public import StratificationTheory.Foundation.ThreePrismSpacetimeFacetCoordinates

public section

open HarmonicMaps

namespace StratificationTheory

/-- A spatial signed cap of a three-dimensional prism splits into the
original signed spatial edge and the original free time coordinate. -/
theorem three_prism_spatial_cap_coordinates (a : Fin 2) (positive : Bool) (x : Domain 2) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let other := Equiv.swap (0 : Fin 2) 1
    cubicalSignedFaceIsometry 2 a.castSucc positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) =
      e.symm (cubicalSignedFaceIsometry 1 a positive
        (b.symm (EuclideanSpace.single (0 : Fin 1) (x (other a)),
          EuclideanSpace.single (0 : Fin 1) 1)), EuclideanSpace.single (0 : Fin 1) (x a)) := by
  intro b e other
  have hCap₂ : b.symm (EuclideanSpace.single (0 : Fin 1) (x (other a)),
      EuclideanSpace.single (0 : Fin 1) 1) = WithLp.toLp 2 ![x (other a), (1 : ℝ)] := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  have hSplit (z : Domain 2) (t : ℝ) : e.symm (z, EuclideanSpace.single (0 : Fin 1) t) =
      WithLp.toLp 2 ![z 0, z 1, t] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  rw [hSplit, hCap₂, hSplit]
  cases positive <;> fin_cases a <;> ext k <;> fin_cases k <;>
    simp [cubicalSignedFaceIsometry_coordinate, other, Fin.last, Equiv.swap_apply_def]

end StratificationTheory
