module

public import StratificationTheory.Foundation.ThreeCoordinatePrismBoundary
public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

public section

open HarmonicMaps

namespace StratificationTheory

/-- The full canonical time faces of the actual common physical boundary
representative retain the complete original normalized three-face maps. -/
theorem three_coordinate_prism_time_face_values {N q : ℕ}
    (w : Fin 2 → Domain N → Ambient q)
    (rep : Fin 2 → Fin N → Domain N → Ambient q)
    (coord : Fin 3 ↪ Fin N) (ε : ℝ) (y : Domain N) (side : Bool) (z : Domain 3) :
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let free := fun z : Domain 3 => if |z 0| < 1 then (0 : Fin 3) else if |z 1| < 1 then 1 else 2
    let E := fun z : Domain 4 =>
      let sp : Domain 3 := WithLp.toLp 2 ![z 0, z 1, z 2]
      if z 3 = -1 then w 0 (P sp) else if z 3 = 1 then w 1 (P sp) else
        (1 - (z 3 + 1) / 2) • rep 0 (coord (free sp)) (P sp) +
          ((z 3 + 1) / 2) • rep 1 (coord (free sp)) (P sp)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
    E (cubicalSignedFaceIsometry 3 (3 : Fin 4) side
      (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = w (if side then 1 else 0) (P z) := by
  intro P free E e
  have hCap : e.symm (z, EuclideanSpace.single (0 : Fin 1) 1) =
      WithLp.toLp 2 ![z 0, z 1, z 2, (1 : ℝ)] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  have hPoint : cubicalSignedFaceIsometry 3 (3 : Fin 4) side
      (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1)) =
      WithLp.toLp 2 ![z 0, z 1, z 2, (if side then 1 else -1 : ℝ)] := by
    rw [hCap]
    cases side <;> ext k <;> fin_cases k <;> simp [cubicalSignedFaceIsometry_coordinate]
  exact (congrArg E hPoint).trans ((three_coordinate_prism_boundary_formulas w rep coord ε y).1 z side)

end StratificationTheory
