module

public import StratificationTheory.Foundation.CoordinateClosedTargetCubeGeometry
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

/-!
# A fixed source ball for the original unit-cube grid

Every reordered unit-coordinate line rectangle lies in one ball whose radius
depends only on the ambient dimension. Radial source extensions can therefore
use this ball without changing their target values by a cutoff.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Topology
namespace StratificationTheory

/-- The unit coordinate cube has a fixed dimension-dependent Euclidean norm
bound, using the actual Euclidean carrier rather than the Pi maximum norm. -/
theorem euclidean_norm_le_dim_of_coordinate_bound {n : ℕ} (x : Domain n)
    (hx : ∀ i : Fin n, |x i| ≤ 1) : ‖x‖ ≤ (n : ℝ) := by
  have hmax : ‖WithLp.ofLp x‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
      simpa only [Real.norm_eq_abs] using hx i
  calc
    ‖x‖ ≤ (n : ℝ) * ‖WithLp.ofLp x‖ := (cube_coordinate_norm_comparison x).2
    _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg n)
    _ = _ := mul_one _

/-- One radius fixed by dimension contains all reordered native unit-cube
line rectangles. No geometric inclusion premise is added to the source data. -/
theorem unit_coordinate_line_rectangle_mem_ball {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (x : Domain n)
    (hx : ∀ i : Fin n, x i ∈ Ioo (-1 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t)) ∈
      ball (0 : Domain (n + 1)) ((n : ℝ) + 2) := by
  let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let y := Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
  have hxn : ‖x‖ ≤ (n : ℝ) := euclidean_norm_le_dim_of_coordinate_bound x
    (fun i => (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩))
  have ht₁ : |t| ≤ 1 := (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have htsq : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr ht₁
  have hnormsq : ‖y‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
    rw [Q.norm_map]
    change ‖e.symm (x, EuclideanSpace.single (0 : Fin 1) t)‖ ^ 2 = _
    rw [norm_sq_finAddEquivProd_symm, PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have hbound : ‖y‖ ≤ (n : ℝ) + 1 := by
    nlinarith only [hnormsq, hxn, norm_nonneg x, norm_nonneg y,
      (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), htsq]
  change y ∈ ball (0 : Domain (n + 1)) ((n : ℝ) + 2)
  rw [mem_ball_zero_iff]
  linarith only [hbound]

end StratificationTheory
