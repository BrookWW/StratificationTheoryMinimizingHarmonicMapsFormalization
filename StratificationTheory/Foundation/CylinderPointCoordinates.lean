module

public import StratificationTheory.Frozen.UnitCylinder
public import StratificationTheory.Foundation.CylinderCoordinateMeasure

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

/-- Actual sphere and closed-interval coordinates determine a point of the
literal physical cylinder. -/
theorem unitCylinder_param_mem {n : ℕ} {a b : ℝ}
    (θ : sphere (0 : Domain n) 1) (t : Icc a b) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
      (θ.val, EuclideanSpace.single (0 : Fin 1) t.val) ∈ unitCylinder n a b := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  change (e (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t.val))).1 ∈
      sphere (0 : Domain n) 1 ∧
    (e (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t.val))).2 0 ∈ Icc a b
  rw [e.apply_symm_apply]
  exact ⟨θ.property, by simp⟩

/-- Every point of the literal cylinder has its original sphere and time
coordinates, with no choice of representative or fallback value. -/
theorem unitCylinder_param_surjective {n : ℕ} {a b : ℝ}
    (c : unitCylinder n a b) :
    ∃ θ : sphere (0 : Domain n) 1, ∃ t : Icc a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) t.val) = c.val := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  exact ⟨⟨(e c.val).1, c.property.1⟩, ⟨(e c.val).2 0, c.property.2⟩,
    cylinder_coordinates_inverse_left n c.val⟩

end StratificationTheory
