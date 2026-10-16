module

public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

public section

open HarmonicMaps

namespace StratificationTheory

/-- The twelve physical edges of the three-dimensional cube have these
literal signed-face chart incidences. Both charts of a shared edge retain
the same original free coordinate. -/
theorem cubical_three_dimensional_edge_charts (positiveFacet positiveEdge : Bool) (x : Domain 1) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let r : ℝ := if positiveFacet then 1 else -1
    let s : ℝ := if positiveEdge then 1 else -1
    let edge := fun (j : Fin 3) (i : Fin 2) => cubicalSignedFaceIsometry 2 j positiveFacet
      (e.symm (cubicalSignedFaceIsometry 1 i positiveEdge
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)), EuclideanSpace.single (0 : Fin 1) 1))
    edge 0 0 = WithLp.toLp 2 ![r, x 0, s] ∧
    edge 0 1 = WithLp.toLp 2 ![r, s, x 0] ∧
    edge 1 0 = WithLp.toLp 2 ![s, r, x 0] ∧
    edge 1 1 = WithLp.toLp 2 ![x 0, r, s] ∧
    edge 2 0 = WithLp.toLp 2 ![s, x 0, r] ∧
    edge 2 1 = WithLp.toLp 2 ![x 0, s, r] := by
  intro b e r s edge
  have hcap₂ : b.symm (x, EuclideanSpace.single (0 : Fin 1) 1) = WithLp.toLp 2 ![x 0, (1 : ℝ)] := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  have hcap₃ (z : Domain 2) : e.symm (z, EuclideanSpace.single (0 : Fin 1) 1) = WithLp.toLp 2 ![z 0, z 1, (1 : ℝ)] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  cases positiveFacet <;> cases positiveEdge
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext k <;> fin_cases k <;>
      simp [edge, r, s, hcap₂, hcap₃, cubicalSignedFaceIsometry_coordinate,
        Equiv.swap_apply_def, Fin.last]

end StratificationTheory
