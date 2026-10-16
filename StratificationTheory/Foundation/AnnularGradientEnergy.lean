module

public import StratificationTheory.Foundation.SphericalProjectionDifferential
public import HarmonicMaps.Analysis.AffineEnergyScaling

/-!
# Energy of tangential and radial annular columns

Tangential projection and a radial rank-one column family are orthogonal in
the actual Hilbert--Schmidt square. This fixes the energy algebra for the
spatial and time columns after annular coordinate transfer.
-/

public section
open HarmonicMaps
open scoped BigOperators RealInnerProductSpace
namespace StratificationTheory

/-- The displayed tangential columns and radial time column have no mixed
term, for arbitrary real scale factors and every unit direction. -/
theorem hsNormSq_annular_columns_eq {n q : ℕ} (θ : Metric.sphere (0 : Domain n) 1)
    (A : Gradient n q) (B : Ambient q) (r τ : ℝ) :
    hsNormSq (fun i => r • tangentialColumns θ A i + τ • (θ.val i • B)) =
      r ^ 2 * hsNormSq (tangentialColumns θ A) + τ ^ 2 * ‖B‖ ^ 2 := by
  have hsum : (∑ i : Fin n, (θ.val i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq,
      mem_sphere_zero_iff_norm.mp θ.property]
    norm_num
  have hcross : (∑ i : Fin n, θ.val i * inner ℝ (tangentialColumns θ A i) B) = 0 := by
    calc
      _ = ∑ i : Fin n, inner ℝ (θ.val i • tangentialColumns θ A i) B :=
        Finset.sum_congr rfl fun i _ => (real_inner_smul_left _ _ _).symm
      _ = inner ℝ (∑ i : Fin n, θ.val i • tangentialColumns θ A i) B :=
        (sum_inner Finset.univ _ B).symm
      _ = 0 := by rw [sum_smul_tangentialColumns_eq_zero, inner_zero_left]
  have hcol (i : Fin n) :
      ‖r • tangentialColumns θ A i + τ • (θ.val i • B)‖ ^ 2 =
        r ^ 2 * ‖tangentialColumns θ A i‖ ^ 2 +
        (2 * r * τ) * (θ.val i * inner ℝ (tangentialColumns θ A i) B) +
        τ ^ 2 * ‖B‖ ^ 2 * (θ.val i) ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [hsNormSq, hcol, Finset.sum_add_distrib, ← Finset.mul_sum,
    hcross, hsum, mul_zero, add_zero, mul_one]

/-- The full annular column square is bounded by the original spatial and
temporal column squares, with their respective reciprocal-length factors. -/
theorem hsNormSq_annular_columns_le {n q : ℕ} (θ : Metric.sphere (0 : Domain n) 1)
    (A : Gradient n q) (B : Ambient q) (r τ : ℝ) :
    hsNormSq (fun i => r • tangentialColumns θ A i + τ • (θ.val i • B)) ≤
      r ^ 2 * hsNormSq A + τ ^ 2 * ‖B‖ ^ 2 := by
  rw [hsNormSq_annular_columns_eq]
  exact add_le_add_left
    (mul_le_mul_of_nonneg_left (hsNormSq_tangentialColumns_le θ A) (sq_nonneg r)) _

/-- When the tangential reciprocal length is no larger than the radial
reciprocal length, one common square factor controls the whole density. -/
theorem hsNormSq_annular_columns_le_common {n q : ℕ}
    (θ : Metric.sphere (0 : Domain n) 1) (A : Gradient n q) (B : Ambient q)
    {r τ : ℝ} (hr : 0 ≤ r) (hrτ : r ≤ τ) :
    hsNormSq (fun i => r • tangentialColumns θ A i + τ • (θ.val i • B)) ≤
      τ ^ 2 * (hsNormSq A + ‖B‖ ^ 2) := by
  calc
    _ ≤ r ^ 2 * hsNormSq A + τ ^ 2 * ‖B‖ ^ 2 := hsNormSq_annular_columns_le θ A B r τ
    _ ≤ τ ^ 2 * hsNormSq A + τ ^ 2 * ‖B‖ ^ 2 :=
      add_le_add_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hr hrτ 2) (hsNormSq_nonneg A)) _
    _ = _ := (mul_add _ _ _).symm

end StratificationTheory
