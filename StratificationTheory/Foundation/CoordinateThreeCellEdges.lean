module

public import StratificationTheory.Foundation.CoordinateCellFacetEmbedding
public import StratificationTheory.Foundation.TwoVectorSquareTraceTransport

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- The original affine three-cell embedding and its two nested canonical
signed charts give exactly the original physical square-edge point. -/
theorem coordinate_three_cell_nested_edge_embedding {N : ℕ}
    (coord : Fin 3 ↪ Fin N) (ε : ℝ) (y : Domain N)
    (i : Fin 3) (sideI : Bool) (a : Fin 2) (sideA : Bool) (x : Domain 1) :
    let pair : Fin 2 ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let origin := y + (if sideI then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let z := cubicalSignedFaceIsometry 1 a sideA (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    let cap := cubicalSignedFaceIsometry 2 i sideI (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))
    let physicalEdge := cubicalSignedFaceIsometry 1 a true
      (b.symm (EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * x 0),
        EuclideanSpace.single (0 : Fin 1) (if sideA then ε else 0)))
    P cap = origin + physicalEdge 0 • EuclideanSpace.single (pair 0) (1 : ℝ) +
      physicalEdge 1 • EuclideanSpace.single (pair 1) (1 : ℝ) := by
  intro pair origin b e P z cap physicalEdge
  have hFirst := coordinate_cell_signed_facet_affine_embedding coord ε y i sideI z
  change P cap = origin + ∑ k : Fin 2,
    (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (pair k) (1 : ℝ) at hFirst
  have hSecond := coordinate_cell_signed_facet_affine_embedding pair ε origin a sideA x
  change (origin + ∑ k : Fin 2, (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (pair k) (1 : ℝ)) =
    (origin + (if sideA then ε else 0) • EuclideanSpace.single (pair a) (1 : ℝ)) +
      ∑ k : Fin 1, (ε / 2 + (ε / 2) * x k) •
        EuclideanSpace.single (pair ((Equiv.swap (Fin.last 1) a) k.castSucc)) (1 : ℝ) at hSecond
  rw [hFirst, hSecond, Fin.sum_univ_one]
  have hEdge := two_vector_square_axis origin (EuclideanSpace.single (pair 0) (1 : ℝ))
    (EuclideanSpace.single (pair 1) (1 : ℝ)) a
    (EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * x 0)) (if sideA then ε else 0)
  fin_cases a <;> simpa [physicalEdge, b, Fin.last] using hEdge.symm

end StratificationTheory
