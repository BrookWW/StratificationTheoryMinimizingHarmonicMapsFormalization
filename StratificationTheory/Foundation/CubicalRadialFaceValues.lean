module

public import StratificationTheory.Foundation.CubicalConeRadialFormula
public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import StratificationTheory.Foundation.CubicalConeGeometry

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- The actual maximum-coordinate radial retraction fixes every point of
each original signed open unit face. -/
theorem cubical_radial_retraction_fixes_unit_face {n : ℕ}
    (i : Fin (n + 1)) (positive : Bool) (x : Domain n)
    (hx : x ∈ ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Q := cubicalSignedFaceIsometry n i positive
    let y := Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    ‖WithLp.ofLp y‖⁻¹ • y = y := by
  intro e Q y
  let z := e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)
  have hTime : (e z).2 0 = 1 := by simp only [z, e.apply_symm_apply, PiLp.single_apply, ite_true]
  have hStrict : ∀ k : Fin n, |(e z).1 k| < (e z).2 0 := by
    intro k
    rw [hTime]
    change |(e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).1 k| < 1
    rw [e.apply_symm_apply]
    exact (mem_unit_coordinate_face_iff x).mp hx k
  have hPositive : 0 < (e z).2 0 := by rw [hTime]; norm_num
  have hFoot : ‖WithLp.ofLp z‖⁻¹ • z = z := by
    rw [(positive_cube_cone_radial_retraction z hPositive hStrict).2]
    change e.symm (((e z).2 0)⁻¹ • (e z).1, EuclideanSpace.single (0 : Fin 1) 1) = z
    simp only [z, e.apply_symm_apply, PiLp.single_apply, ite_true, inv_one, one_smul]
  change ‖WithLp.ofLp (Q z)‖⁻¹ • Q z = Q z
  rw [cubical_radial_retraction_isometry Q (cubicalSignedFaceIsometry_coordinate_norm i positive), hFoot]

/-- A radial cube map takes its exact original boundary representative
value on every signed open face, pointwise on the complete open base. -/
theorem cubical_radial_map_unit_face_value {n q : ℕ}
    (G : Domain (n + 1) → Ambient q) (i : Fin (n + 1)) (positive : Bool) (x : Domain n)
    (hx : x ∈ ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let y := cubicalSignedFaceIsometry n i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    G (‖WithLp.ofLp y‖⁻¹ • y) = G y :=
  congrArg G (cubical_radial_retraction_fixes_unit_face i positive x hx)

end StratificationTheory
