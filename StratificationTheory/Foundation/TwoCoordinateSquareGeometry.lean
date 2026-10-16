module

public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry

/-!
# Literal two-coordinate source square formulas

The original two-vector affine square and its native coordinate axes have
the same physical edge parameters. Reordered complementary coordinates
are recovered as the corresponding original ambient coordinates.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The first factor of a reordered native split is the literal family of
the original complementary coordinate projections. -/
theorem coordinate_split_first_eq {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Domain (n + 1)) (i : Fin n) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (e (Q.symm x)).1 i = x (p (Fin.castAdd 1 i)) := by
  intro Q e
  change (Q.symm x) (Fin.castAdd 1 i) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- The whole positive square axis chart has the displayed physical two
coordinates for every spatial and normal real parameter. -/
theorem positive_square_axis_coordinates (i : Fin 2) (x : Domain 1) (t : ℝ) :
    cubicalSignedFaceIsometry 1 i true
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t)) =
      if i = 0 then WithLp.toLp 2 ![t, x 0] else WithLp.toLp 2 ![x 0, t] := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  have hcap : e.symm (x, EuclideanSpace.single (0 : Fin 1) t) = WithLp.toLp 2 ![x 0, t] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  rw [hcap]
  ext j
  fin_cases i <;> fin_cases j <;> simp [cubicalSignedFaceIsometry_coordinate, Fin.last]

/-- Each original affine square coordinate line is the literal normal
translation followed by the complementary source coordinate direction. -/
theorem two_vector_square_axis {N : ℕ} (y v₀ v₁ : Domain N)
    (i : Fin 2) (x : Domain 1) (t : ℝ) :
    let z := cubicalSignedFaceIsometry 1 i true
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t))
    y + z 0 • v₀ + z 1 • v₁ =
      (y + t • (if i = 0 then v₀ else v₁)) + x 0 • (if i = 0 then v₁ else v₀) := by
  intro z
  dsimp only [z]
  rw [positive_square_axis_coordinates]
  fin_cases i
  · rfl
  · change y + x 0 • v₀ + t • v₁ = y + t • v₁ + x 0 • v₀
    abel

end StratificationTheory
