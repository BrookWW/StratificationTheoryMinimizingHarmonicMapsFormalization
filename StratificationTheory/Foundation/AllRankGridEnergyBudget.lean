module

public import StratificationTheory.Foundation.CubicalNearLevelLatticeIncidence

/-! # A common quantitative invariant for every original face rank -/

public section
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- Every original gradient rank has the same final mesh-width factor
under the physical prism coefficient, including rank-one edges. -/
theorem native_rank_prism_scaling_cancel {m d : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hd : d ≤ m) :
    ENNReal.ofReal (ε ^ (m - d + 1)) * (ENNReal.ofReal (ε ^ m))⁻¹ *
      ENNReal.ofReal (ε ^ d) = ENNReal.ofReal ε := by
  simp only [ENNReal.ofReal_pow hε.le]
  let x := ENNReal.ofReal ε
  have hx0 : x ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hxFinite : x ≠ ⊤ := ENNReal.ofReal_ne_top
  change x ^ (m - d + 1) * (x ^ m)⁻¹ * x ^ d = x
  calc
    _ = (x ^ (m - d + 1) * x ^ d) * (x ^ m)⁻¹ := by ac_rfl
    _ = x ^ (m + 1) * (x ^ m)⁻¹ := by
      rw [← pow_add, show m - d + 1 + d = m + 1 by omega]
    _ = (x ^ m * (x ^ m)⁻¹) * x := by rw [pow_succ]; ac_rfl
    _ = x := by rw [ENNReal.mul_inv_cancel (pow_ne_zero m hx0) (ENNReal.pow_ne_top hxFinite), one_mul]

/-- The original one-face discrepancy has precisely the reciprocal mesh
width under the full physical prism coefficient. -/
theorem native_edge_discrepancy_prism_scaling_cancel {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε ^ n) * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ENNReal.ofReal ε = (ENNReal.ofReal ε)⁻¹ := by
  simp only [ENNReal.ofReal_pow hε.le]
  let x := ENNReal.ofReal ε
  have hx0 : x ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hxFinite : x ≠ ⊤ := ENNReal.ofReal_ne_top
  change x ^ n * (x ^ (n + 2))⁻¹ * x = x⁻¹
  apply (ENNReal.mul_left_inj hx0 hxFinite).mp
  calc
    _ = x ^ (n + 2) * (x ^ (n + 2))⁻¹ := by rw [pow_add, pow_two]; ac_rfl
    _ = 1 := ENNReal.mul_inv_cancel (pow_ne_zero _ hx0) (ENNReal.pow_ne_top hxFinite)
    _ = x⁻¹ * x := (ENNReal.inv_mul_cancel hx0 hxFinite).symm

/-- Finite actual lattice incidences of every original gradient rank obey
one common energy budget. The horizontal source energy at each rank is
included with its physical coefficient. -/
theorem all_rank_finite_grid_energy_budget {m : ℕ} {G I J : Type*}
    [AddGroup G] [Fintype I] {ε : ℝ} (hε : 0 < ε)
    (rank : J → ℕ) (hRank : ∀ j, rank j ≤ m) (index : I → J) (shift : I → G)
    (channel : J → G → ℝ≥0∞) (count : ℕ) (A₀ : ℝ≥0∞)
    (hChannel : ∀ j, (∑' z : G, channel j z) ≤
      2 * (ENNReal.ofReal (ε ^ m))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal (ε ^ rank j)) * A₀) :
    (∑' z : G, ∑ i : I, ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) *
      channel (index i) (z + shift i)) ≤
        2 * (count : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞) * ENNReal.ofReal ε * A₀ := by
  rw [tsum_finite_lattice_shift_channels shift
    (fun i z => ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) * channel (index i) z)]
  simp_rw [ENNReal.tsum_mul_left]
  have hOne (i : I) : ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) *
      (∑' z : G, channel (index i) z) ≤ 2 * (count : ℝ≥0∞) * ENNReal.ofReal ε * A₀ := by
    calc
      _ ≤ ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) *
          (2 * (ENNReal.ofReal (ε ^ m))⁻¹ * ((count : ℝ≥0∞) *
            ENNReal.ofReal (ε ^ rank (index i))) * A₀) := mul_le_mul_right (hChannel (index i)) _
      _ = 2 * (count : ℝ≥0∞) * (ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) *
          (ENNReal.ofReal (ε ^ m))⁻¹ * ENNReal.ofReal (ε ^ rank (index i))) * A₀ := by ac_rfl
      _ = _ := by rw [native_rank_prism_scaling_cancel hε (hRank (index i))]
  calc
    _ ≤ ∑ _i : I, (2 * (count : ℝ≥0∞) * ENNReal.ofReal ε * A₀) := Finset.sum_le_sum fun i _ => hOne i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ac_rfl

/-- The same finite actual lattice-incidence count handles the original
rank-one discrepancy with the physical reciprocal-width energy factor. -/
theorem edge_finite_grid_discrepancy_budget {n : ℕ} {G I J : Type*}
    [AddGroup G] [Fintype I] {ε : ℝ} (hε : 0 < ε)
    (index : I → J) (shift : I → G) (channel : J → G → ℝ≥0∞) (count : ℕ) (D₀ : ℝ≥0∞)
    (hChannel : ∀ j, (∑' z : G, channel j z) ≤
      2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal ε) * D₀) :
    (∑' z : G, ∑ i : I, ENNReal.ofReal (ε ^ n) * channel (index i) (z + shift i)) ≤
      2 * (count : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞) * (ENNReal.ofReal ε)⁻¹ * D₀ := by
  rw [tsum_finite_lattice_shift_channels shift
    (fun i z => ENNReal.ofReal (ε ^ n) * channel (index i) z)]
  simp_rw [ENNReal.tsum_mul_left]
  have hOne (i : I) : ENNReal.ofReal (ε ^ n) * (∑' z : G, channel (index i) z) ≤
      2 * (count : ℝ≥0∞) * (ENNReal.ofReal ε)⁻¹ * D₀ := by
    calc
      _ ≤ ENNReal.ofReal (ε ^ n) * (2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
          ((count : ℝ≥0∞) * ENNReal.ofReal ε) * D₀) := mul_le_mul_right (hChannel (index i)) _
      _ = 2 * (count : ℝ≥0∞) * (ENNReal.ofReal (ε ^ n) *
          (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ENNReal.ofReal ε) * D₀ := by ac_rfl
      _ = _ := by rw [native_edge_discrepancy_prism_scaling_cancel hε]
  calc
    _ ≤ ∑ _i : I, (2 * (count : ℝ≥0∞) * (ENNReal.ofReal ε)⁻¹ * D₀) := Finset.sum_le_sum fun i _ => hOne i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ac_rfl

end StratificationTheory
