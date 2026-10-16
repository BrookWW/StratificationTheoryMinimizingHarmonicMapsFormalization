module

public import StratificationTheory.Foundation.ThreeCoordinatePrismEdgeValues
public import StratificationTheory.Foundation.ThreePrismSpatialCapCoordinates
public import StratificationTheory.Foundation.AffineEdgeCanonicalFaceValues

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- The common physical boundary representative takes the exact original
normalized affine edge value on every spatial cap of each first prism. -/
theorem three_coordinate_prism_spatial_facet_edge_values {N q : ℕ}
    (w : Fin 2 → Domain N → Ambient q)
    (rep : Fin 2 → Fin N → Domain N → Ambient q)
    (coord : Fin 3 ↪ Fin N) {ε : ℝ} (hε : 0 < ε) (y : Domain N)
    (i : Fin 3) (sideI : Bool) :
    let pair : Fin 2 ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let origin := y + (if sideI then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
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
    let edgePoint := fun (a : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 a true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let F := fun a side l s => rep l (pair ((Equiv.swap (0 : Fin 2) 1) a)) (embed (edgePoint a side s))
    let T := fun z : Domain 2 => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let V := fun (a : Fin 2) (side : Bool) (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F a side 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F a side 1 ((b (T z)).1 0)
    let A := cubicalSignedFaceIsometry 2 i true
    let facet := fun z : Domain 3 => cubicalSignedFaceIsometry 3 i.castSucc sideI
      (e₃.symm (A z, EuclideanSpace.single (0 : Fin 1) 1))
    ∀ (a : Fin 2) (positive : Bool) (x : Domain 2),
      x ∈ ⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1 →
      E (facet (cubicalSignedFaceIsometry 2 a.castSucc positive
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) =
        V a positive (cubicalSignedFaceIsometry 1 a true x) := by
  intro pair origin b e e₃ P free E embed edgePoint F T V A facet a positive x hx
  have hX (z : Domain 3) : facet z = WithLp.toLp 2 ![
      (cubicalSignedFaceIsometry 2 i sideI (e.symm ((e z).1, EuclideanSpace.single (0 : Fin 1) 1))) 0,
      (cubicalSignedFaceIsometry 2 i sideI (e.symm ((e z).1, EuclideanSpace.single (0 : Fin 1) 1))) 1,
      (cubicalSignedFaceIsometry 2 i sideI (e.symm ((e z).1, EuclideanSpace.single (0 : Fin 1) 1))) 2,
      (e z).2 0] := three_prism_spacetime_spatial_facet_coordinates i sideI z
  have hx' (k : Fin 2) : x k ∈ Ioo (-1 : ℝ) 1 := mem_iInter.mp hx k
  let other := Equiv.swap (0 : Fin 2) 1
  rw [three_prism_spatial_cap_coordinates]
  rw [hX, e.apply_symm_apply]
  simp only [PiLp.single_apply, ite_true]
  have hEdge := three_coordinate_prism_boundary_matches_edge_connector w rep coord ε y i sideI a positive
    (EuclideanSpace.single (0 : Fin 1) (x (other a))) (x a) (hx' (other a)) (hx' a)
  change E _ = _ at hEdge
  rw [hEdge]
  change (1 - (x a + 1) / 2) • F a positive 0 (ε / 2 + (ε / 2) * x (other a)) +
    ((x a + 1) / 2) • F a positive 1 (ε / 2 + (ε / 2) * x (other a)) = _
  dsimp only [V]
  generalize hF : F = F₀
  exact (affine_edge_canonical_face_value hε F₀ a positive x).symm

end StratificationTheory
