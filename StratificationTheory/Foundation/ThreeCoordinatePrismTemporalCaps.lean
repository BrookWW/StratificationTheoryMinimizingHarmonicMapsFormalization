module

public import StratificationTheory.Foundation.ThreeCoordinatePrismBoundary
public import StratificationTheory.Foundation.CoordinateCellFacetEmbedding
public import StratificationTheory.Foundation.ThreePrismSpacetimeFacetCoordinates
public import StratificationTheory.Foundation.CubicalSignedFrameBlock

public section

open HarmonicMaps

namespace StratificationTheory

/-- The same physical boundary representative takes the original raw
normalized square map on both time caps of each actual first-prism facet. -/
theorem three_coordinate_prism_facet_temporal_cap_values {N q : ℕ}
    (w : Fin 2 → Domain N → Ambient q)
    (rep : Fin 2 → Fin N → Domain N → Ambient q)
    (coord : Fin 3 ↪ Fin N) (ε : ℝ) (y : Domain N)
    (i : Fin 3) (sideI positive : Bool) (x : Domain 2) :
    let pair : Fin 2 ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let origin := y + (if sideI then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let e₃ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let free := fun z : Domain 3 => if |z 0| < 1 then (0 : Fin 3) else if |z 1| < 1 then 1 else 2
    let E := fun z : Domain 4 =>
      let sp : Domain 3 := WithLp.toLp 2 ![z 0, z 1, z 2]
      if z 3 = -1 then w 0 (P sp) else if z 3 = 1 then w 1 (P sp) else
        (1 - (z 3 + 1) / 2) • rep 0 (coord (free sp)) (P sp) +
          ((z 3 + 1) / 2) • rep 1 (coord (free sp)) (P sp)
    let embed := fun t : Domain 2 => origin + t 0 • EuclideanSpace.single (pair 0) (1 : ℝ) +
      t 1 • EuclideanSpace.single (pair 1) (1 : ℝ)
    let T := fun z : Domain 2 => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let U := fun side : Bool => w (if side then 1 else 0) ∘ embed ∘ T
    let A := cubicalSignedFaceIsometry 2 i true
    let facet := fun z : Domain 3 => cubicalSignedFaceIsometry 3 i.castSucc sideI
      (e₃.symm (A z, EuclideanSpace.single (0 : Fin 1) 1))
    E (facet (cubicalSignedFaceIsometry 2 (2 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) = U positive x := by
  intro pair origin e e₃ P free E embed T U A facet
  have hId (v : Domain 3) : cubicalSignedFaceIsometry 2 (2 : Fin 3) true v = v := by
    ext k
    fin_cases k <;> simp [cubicalSignedFaceIsometry_coordinate]
  have hCap : cubicalSignedFaceIsometry 2 (2 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) =
      e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then 1 else -1)) := by
    rw [cubical_signed_face_native_height, hId]
  let sp := cubicalSignedFaceIsometry 2 i sideI (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
  have hFirstPoint : facet (cubicalSignedFaceIsometry 2 (2 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) =
      WithLp.toLp 2 ![sp 0, sp 1, sp 2, (if positive then 1 else -1 : ℝ)] := by
    rw [hCap]
    have hX := three_prism_spacetime_spatial_facet_coordinates i sideI
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then 1 else -1)))
    change facet _ = _ at hX
    rw [hX, e.apply_symm_apply]
    rfl
  have hHorizontal : E (WithLp.toLp 2 ![sp 0, sp 1, sp 2, (if positive then 1 else -1 : ℝ)]) =
      w (if positive then 1 else 0) (P sp) :=
    (three_coordinate_prism_boundary_formulas w rep coord ε y).1 sp positive
  have hPoint := coordinate_cell_signed_facet_affine_embedding coord ε y i sideI x
  change P sp = origin + ∑ k : Fin 2, (ε / 2 + (ε / 2) * x k) •
    EuclideanSpace.single (pair k) (1 : ℝ) at hPoint
  have hPoint' : P sp = embed (T x) := by
    rw [hPoint, Fin.sum_univ_two]
    change origin + ((ε / 2 + (ε / 2) * x 0) • EuclideanSpace.single (pair 0) (1 : ℝ) +
      (ε / 2 + (ε / 2) * x 1) • EuclideanSpace.single (pair 1) (1 : ℝ)) =
      (origin + (ε / 2 + (ε / 2) * x 0) • EuclideanSpace.single (pair 0) (1 : ℝ)) +
        (ε / 2 + (ε / 2) * x 1) • EuclideanSpace.single (pair 1) (1 : ℝ)
    exact (add_assoc origin _ _).symm
  exact (congrArg E hFirstPoint).trans (hHorizontal.trans (congrArg (w (if positive then 1 else 0)) hPoint'))

end StratificationTheory
