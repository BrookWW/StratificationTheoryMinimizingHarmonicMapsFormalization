module

public import StratificationTheory.Foundation.ThreeCoordinatePrismBoundary
public import StratificationTheory.Foundation.CoordinateThreeCellEdges
public import StratificationTheory.Foundation.CubicalThreeDimensionalIncidence

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- On every open spatial edge times the open time interval, the same
three-coordinate physical boundary representative is exactly the affine
connector formed from the original directional representatives of that
physical square edge. -/
theorem three_coordinate_prism_boundary_matches_edge_connector {N q : ℕ}
    (w : Fin 2 → Domain N → Ambient q)
    (rep : Fin 2 → Fin N → Domain N → Ambient q)
    (coord : Fin 3 ↪ Fin N) (ε : ℝ) (y : Domain N)
    (i : Fin 3) (sideI : Bool) (a : Fin 2) (sideA : Bool) (x : Domain 1) (t : ℝ)
    (hx : x 0 ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    let pair : Fin 2 ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let origin := y + (if sideI then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let free := fun z : Domain 3 => if |z 0| < 1 then (0 : Fin 3) else if |z 1| < 1 then 1 else 2
    let X := fun (z : Domain 3) (η : ℝ) => WithLp.toLp 2 ![z 0, z 1, z 2, η]
    let E := fun z : Domain 4 =>
      let sp : Domain 3 := WithLp.toLp 2 ![z 0, z 1, z 2]
      if z 3 = -1 then w 0 (P sp) else if z 3 = 1 then w 1 (P sp) else
        (1 - (z 3 + 1) / 2) • rep 0 (coord (free sp)) (P sp) +
          ((z 3 + 1) / 2) • rep 1 (coord (free sp)) (P sp)
    let z := cubicalSignedFaceIsometry 1 a sideA (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    let cap := cubicalSignedFaceIsometry 2 i sideI (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))
    let physicalEdge := cubicalSignedFaceIsometry 1 a true
      (b.symm (EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * x 0),
        EuclideanSpace.single (0 : Fin 1) (if sideA then ε else 0)))
    let point := origin + physicalEdge 0 • EuclideanSpace.single (pair 0) (1 : ℝ) +
      physicalEdge 1 • EuclideanSpace.single (pair 1) (1 : ℝ)
    let tangent := pair ((Equiv.swap (0 : Fin 2) 1) a)
    E (X cap t) = (1 - (t + 1) / 2) • rep 0 tangent point +
      ((t + 1) / 2) • rep 1 tangent point := by
  intro pair origin b e P free X E z cap physicalEdge point tangent
  have hSpatial (z₀ : Domain 3) (η : ℝ) :
      (WithLp.toLp 2 ![(X z₀ η) 0, (X z₀ η) 1, (X z₀ η) 2] : Domain 3) = z₀ := by
    ext k
    fin_cases k <;> rfl
  have hTime : (X cap t) 3 = t := rfl
  have hPoint : P cap = point := coordinate_three_cell_nested_edge_embedding coord ε y i sideI a sideA x
  have hIndex : coord (free cap) = tangent := by
    have hCharts := cubical_three_dimensional_edge_charts sideI sideA x
    have hr : ¬ |(if sideI then 1 else -1 : ℝ)| < 1 := by cases sideI <;> norm_num
    have hs : ¬ |(if sideA then 1 else -1 : ℝ)| < 1 := by cases sideA <;> norm_num
    have hx' : |x 0| < 1 := abs_lt.mpr hx
    fin_cases i <;> fin_cases a
    · change coord (free _) = tangent
      rw [show cap = _ from hCharts.1]
      simp [free, tangent, pair, hr, hx', Fin.last, Equiv.swap_apply_def]
    · rw [show cap = _ from hCharts.2.1]
      simp [free, tangent, pair, hr, hs, Fin.last]
    · rw [show cap = _ from hCharts.2.2.1]
      simp [free, tangent, pair, hr, hs, Fin.last]
    · rw [show cap = _ from hCharts.2.2.2.1]
      simp [free, tangent, pair, hx', Fin.last, Equiv.swap_apply_def]
    · rw [show cap = _ from hCharts.2.2.2.2.1]
      simp [free, tangent, pair, hs, hx', Fin.last]
    · rw [show cap = _ from hCharts.2.2.2.2.2]
      simp [free, tangent, pair, hx', Fin.last]
  dsimp only [E]
  rw [hSpatial, hTime, if_neg (ne_of_gt ht.1), if_neg (ne_of_lt ht.2), hIndex, hPoint]

end StratificationTheory
