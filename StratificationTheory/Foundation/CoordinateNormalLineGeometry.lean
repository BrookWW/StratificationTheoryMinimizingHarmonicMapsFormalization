module

public import StratificationTheory.Foundation.CubicalFaceSobolevQualification
public import StratificationTheory.Foundation.CylinderCoordinateMeasure

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The last coordinate of a reordered Euclidean split is the corresponding
original ambient coordinate. -/
theorem coordinate_split_last_eq {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Domain (n + 1)) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (e (Q.symm x)).2 0 = x (p (Fin.natAdd n (0 : Fin 1))) := by
  intro Q e
  have hlast (v : Domain (n + 1)) : (e v).2 0 = v (Fin.natAdd n (0 : Fin 1)) := by
    simp [e, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp]
  rw [hlast]
  change ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p).symm x) _ = _
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- Changing the last coordinate in a reordered split is literal translation
along its original ambient coordinate direction. -/
theorem coordinate_line_eq_add_normal {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Domain (n + 1)) (t : ℝ) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    Q (e.symm ((e (Q.symm x)).1, EuclideanSpace.single (0 : Fin 1) t)) =
      x + (t - x (p (Fin.natAdd n (0 : Fin 1)))) •
        EuclideanSpace.single (p (Fin.natAdd n (0 : Fin 1))) (1 : ℝ) := by
  intro Q e
  let β := (e (Q.symm x)).1
  let T := (e (Q.symm x)).2 0
  have hrec : Q (e.symm (β, EuclideanSpace.single (0 : Fin 1) T)) = x := by
    rw [cylinder_coordinates_inverse_left n (Q.symm x), Q.apply_symm_apply]
  have hpair : (β, EuclideanSpace.single (0 : Fin 1) t) =
      (β, EuclideanSpace.single (0 : Fin 1) T) +
        (0, EuclideanSpace.single (0 : Fin 1) (t - T)) := by
    apply Prod.ext
    · exact (add_zero β).symm
    · ext j
      fin_cases j
      simp
  change Q (e.symm (β, EuclideanSpace.single (0 : Fin 1) t)) = _
  rw [hpair, map_add, map_add, hrec, coordinate_face_embedding_eq_sum]
  simp only [Fin.sum_univ_one]
  have hT : T = x (p (Fin.natAdd n (0 : Fin 1))) := coordinate_split_last_eq p x
  simp only [PiLp.single_apply, ite_true, hT]

/-- Normal translations preserve the complementary raw coordinates and add
their physical amount to the original normal coordinate. -/
theorem coordinate_normal_translation_coordinates {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (x : Domain (n + 1)) (s : ℝ) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let v := EuclideanSpace.single (p (Fin.natAdd n (0 : Fin 1))) (1 : ℝ)
    (e (Q.symm (x + s • v))).1 = (e (Q.symm x)).1 ∧
      (e (Q.symm (x + s • v))).2 0 =
        x (p (Fin.natAdd n (0 : Fin 1))) + s := by
  intro Q e v
  have hline := coordinate_line_eq_add_normal p x
    (x (p (Fin.natAdd n (0 : Fin 1))) + s)
  simp only [add_sub_cancel_left] at hline
  change Q (e.symm ((e (Q.symm x)).1,
    EuclideanSpace.single (0 : Fin 1) (x (p (Fin.natAdd n (0 : Fin 1))) + s))) = x + s • v at hline
  rw [← hline]
  simp only [Q.symm_apply_apply, e.apply_symm_apply, PiLp.single_apply, ite_true, and_self]

end StratificationTheory
