module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Radial coordinates of the actual cube boundary

The maximum coordinate norm is the literal norm of the underlying Pi function.
It gives the radial cube-boundary map and its inverse Euclidean normalization.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators
namespace StratificationTheory

/-- The maximum coordinate norm is bounded by the Euclidean norm, which is
bounded by the dimension times the maximum coordinate norm. -/
theorem cube_coordinate_norm_comparison {n : ℕ} (x : Domain n) :
    ‖WithLp.ofLp x‖ ≤ ‖x‖ ∧ ‖x‖ ≤ (n : ℝ) * ‖WithLp.ofLp x‖ := by
  have hmax : ‖WithLp.ofLp x‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    exact PiLp.norm_apply_le x i
  refine ⟨hmax, ?_⟩
  have hrepr : (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  calc
    ‖x‖ = ‖∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)‖ := congrArg norm hrepr.symm
    _ ≤ ∑ i : Fin n, ‖x i • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖WithLp.ofLp x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
      exact norm_le_pi_norm (WithLp.ofLp x) i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The radial maximum norm varies with Euclidean Lipschitz constant one. -/
theorem cube_coordinate_norm_sub_le {n : ℕ} (x y : Domain n) :
    |‖WithLp.ofLp x‖ - ‖WithLp.ofLp y‖| ≤ ‖x - y‖ := by
  exact (abs_norm_sub_norm_le (WithLp.ofLp x) (WithLp.ofLp y)).trans
    (cube_coordinate_norm_comparison (x - y)).1

private theorem cube_coordinate_norm_pos {n : ℕ} {x : Domain n} (hx : x ≠ 0) :
    0 < ‖WithLp.ofLp x‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply hx
  exact (WithLp.equiv 2 (Fin n → ℝ)).injective hz

private theorem cube_coordinate_norm_smul {n : ℕ} (r : ℝ) (x : Domain n) :
    ‖WithLp.ofLp (r • x)‖ = |r| * ‖WithLp.ofLp x‖ := by
  rw [WithLp.ofLp_smul, norm_smul, Real.norm_eq_abs]

private theorem norm_scaled_difference_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) (a b : ℝ) :
    ‖a • x - b • y‖ ≤ |a| * ‖x - y‖ + |a - b| * ‖y‖ := by
  have heq : a • x - b • y = a • (x - y) + (a - b) • y := by
    rw [smul_sub, sub_smul]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])

private theorem abs_inverse_sub_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| = a⁻¹ * b⁻¹ * |a - b| := by
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_sub_comm,
    abs_of_pos (mul_pos ha hb)]
  field_simp

private theorem norm_normalize_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤
      2 * ‖x‖⁻¹ * ‖x - y‖ := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := norm_scaled_difference_le x y ‖x‖⁻¹ ‖y‖⁻¹
  rw [abs_of_pos (inv_pos.mpr hnx), abs_inverse_sub_of_pos hnx hny] at h
  have heq : (‖x‖⁻¹ * ‖y‖⁻¹ * |‖x‖ - ‖y‖|) * ‖y‖ =
      ‖x‖⁻¹ * |‖x‖ - ‖y‖| := by
    field_simp
  rw [heq] at h
  calc
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * |‖x‖ - ‖y‖| := h
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * ‖x - y‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y)
        (inv_nonneg.mpr (norm_nonneg x)))
    _ = _ := by ring

/-- The radial map from the unit Euclidean sphere to a cube of radius r
has a dimension-dependent Euclidean Lipschitz bound. -/
theorem cube_radial_projection_dist_le {n : ℕ} {r : ℝ} (hr : 0 < r)
    (θ η : sphere (0 : Domain n) 1) :
    dist ((r / ‖WithLp.ofLp θ.val‖) • θ.val)
      ((r / ‖WithLp.ofLp η.val‖) • η.val) ≤
      r * ((n : ℝ) + (n : ℝ) ^ 2) * dist θ.val η.val := by
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hη : ‖η.val‖ = 1 := mem_sphere_zero_iff_norm.mp η.property
  have hθ0 : θ.val ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hθ
    exact zero_ne_one hθ
  have hη0 : η.val ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hη
    exact zero_ne_one hη
  have hgθ := cube_coordinate_norm_pos hθ0
  have hgη := cube_coordinate_norm_pos hη0
  have hinvθ : ‖WithLp.ofLp θ.val‖⁻¹ ≤ (n : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hgθ).mpr
    simpa only [hθ] using (cube_coordinate_norm_comparison θ.val).2
  have hinvη : ‖WithLp.ofLp η.val‖⁻¹ ≤ (n : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hgη).mpr
    simpa only [hη] using (cube_coordinate_norm_comparison η.val).2
  have hscale : |r / ‖WithLp.ofLp θ.val‖| ≤ r * (n : ℝ) := by
    rw [abs_of_pos (div_pos hr hgθ), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinvθ hr.le
  have hdiff : |r / ‖WithLp.ofLp θ.val‖ - r / ‖WithLp.ofLp η.val‖| ≤
      r * (n : ℝ) ^ 2 * ‖θ.val - η.val‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul,
      abs_of_pos hr, abs_inverse_sub_of_pos hgθ hgη]
    calc
      _ ≤ r * ((n : ℝ) * (n : ℝ) * ‖θ.val - η.val‖) := by
        gcongr
        exact cube_coordinate_norm_sub_le θ.val η.val
      _ = _ := by ring
  rw [dist_eq_norm, dist_eq_norm]
  calc
    _ ≤ |r / ‖WithLp.ofLp θ.val‖| * ‖θ.val - η.val‖ +
        |r / ‖WithLp.ofLp θ.val‖ - r / ‖WithLp.ofLp η.val‖| * ‖η.val‖ :=
      norm_scaled_difference_le θ.val η.val _ _
    _ ≤ r * (n : ℝ) * ‖θ.val - η.val‖ + r * (n : ℝ) ^ 2 * ‖θ.val - η.val‖ := by
      rw [hη, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_right hscale (norm_nonneg _)) hdiff
    _ = _ := by ring

/-- Euclidean normalization is the inverse cube-boundary radial map and has
Lipschitz constant at most 2/r on that boundary. -/
theorem cube_boundary_normalize_dist_le {n : ℕ} {r : ℝ} (hr : 0 < r)
    (x y : {x : Domain n // ‖WithLp.ofLp x‖ = r}) :
    dist (NormedSpace.normalize x.val) (NormedSpace.normalize y.val) ≤
      (2 / r) * dist x.val y.val := by
  have hx0 : x.val ≠ 0 := by
    intro hz
    have hh := x.property
    rw [hz, WithLp.ofLp_zero, norm_zero] at hh
    exact hr.ne' hh.symm
  have hy0 : y.val ≠ 0 := by
    intro hz
    have hh := y.property
    rw [hz, WithLp.ofLp_zero, norm_zero] at hh
    exact hr.ne' hh.symm
  have hrle : r ≤ ‖x.val‖ := by
    calc
      r = ‖WithLp.ofLp x.val‖ := x.property.symm
      _ ≤ ‖x.val‖ := (cube_coordinate_norm_comparison x.val).1
  have hinv : ‖x.val‖⁻¹ ≤ r⁻¹ :=
    (inv_le_inv₀ (norm_pos_iff.mpr hx0) hr).mpr hrle
  rw [dist_eq_norm, dist_eq_norm]
  calc
    _ ≤ 2 * ‖x.val‖⁻¹ * ‖x.val - y.val‖ := norm_normalize_sub_le hx0 hy0
    _ ≤ 2 * r⁻¹ * ‖x.val - y.val‖ := by
      gcongr
    _ = _ := by rw [div_eq_mul_inv]

/-- Positive cube radii give literal inverse radial coordinates between the
Euclidean unit sphere and the maximum-coordinate-norm cube boundary. -/
theorem cube_radial_projection_inverse {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (∀ θ : sphere (0 : Domain n) 1,
      ‖WithLp.ofLp ((r / ‖WithLp.ofLp θ.val‖) • θ.val)‖ = r ∧
      NormedSpace.normalize ((r / ‖WithLp.ofLp θ.val‖) • θ.val) = θ.val) ∧
    ∀ x : {x : Domain n // ‖WithLp.ofLp x‖ = r},
      (r / ‖WithLp.ofLp (NormedSpace.normalize x.val)‖) •
        NormedSpace.normalize x.val = x.val := by
  constructor
  · intro θ
    have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    have hθ0 : θ.val ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hθ
      exact zero_ne_one hθ
    have hg := cube_coordinate_norm_pos hθ0
    constructor
    · rw [cube_coordinate_norm_smul, abs_of_pos (div_pos hr hg), div_mul_cancel₀ r hg.ne']
    · rw [NormedSpace.normalize_smul_of_pos (div_pos hr hg),
        NormedSpace.normalize_eq_self_of_norm_eq_one hθ]
  · intro x
    have hx0 : x.val ≠ 0 := by
      intro hz
      have hh := x.property
      rw [hz, WithLp.ofLp_zero, norm_zero] at hh
      exact hr.ne' hh.symm
    have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr hx0
    have hg : ‖WithLp.ofLp (NormedSpace.normalize x.val)‖ = ‖x.val‖⁻¹ * r := by
      rw [NormedSpace.normalize, cube_coordinate_norm_smul,
        abs_of_pos (inv_pos.mpr hn), x.property]
    rw [hg, NormedSpace.normalize, smul_smul]
    have hscalar : r / (‖x.val‖⁻¹ * r) * ‖x.val‖⁻¹ = 1 := by
      field_simp [hr.ne', hn.ne']
    rw [hscalar, one_smul]

/-- The literal radial formulas define an actual bi-Lipschitz homeomorphism
between the Euclidean unit sphere and the maximum-coordinate-norm boundary. -/
theorem exists_cube_radial_bilipschitz_homeomorph {n : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ H : sphere (0 : Domain n) 1 ≃ₜ {x : Domain n // ‖WithLp.ofLp x‖ = r},
      (∀ θ, (H θ).val = (r / ‖WithLp.ofLp θ.val‖) • θ.val) ∧
      (∀ x, (H.symm x).val = NormedSpace.normalize x.val) ∧
      LipschitzWith (Real.toNNReal (r * ((n : ℝ) + (n : ℝ) ^ 2))) H ∧
      LipschitzWith (Real.toNNReal (2 / r)) H.symm := by
  let f : sphere (0 : Domain n) 1 → {x : Domain n // ‖WithLp.ofLp x‖ = r} := fun θ =>
    ⟨(r / ‖WithLp.ofLp θ.val‖) • θ.val, (cube_radial_projection_inverse hr).1 θ |>.1⟩
  have hx0 (x : {x : Domain n // ‖WithLp.ofLp x‖ = r}) : x.val ≠ 0 := by
    intro hz
    have hh := x.property
    rw [hz, WithLp.ofLp_zero, norm_zero] at hh
    exact hr.ne' hh.symm
  let g : {x : Domain n // ‖WithLp.ofLp x‖ = r} → sphere (0 : Domain n) 1 := fun x =>
    ⟨NormedSpace.normalize x.val, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hx0 x))⟩
  have hf : LipschitzWith (Real.toNNReal (r * ((n : ℝ) + (n : ℝ) ^ 2))) f := by
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    rw [Real.coe_toNNReal _ (mul_nonneg hr.le (add_nonneg (Nat.cast_nonneg n) (sq_nonneg _)))]
    exact cube_radial_projection_dist_le hr θ η
  have hg : LipschitzWith (Real.toNNReal (2 / r)) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal _ (div_nonneg (by norm_num) hr.le)]
    exact cube_boundary_normalize_dist_le hr x y
  let H : sphere (0 : Domain n) 1 ≃ₜ {x : Domain n // ‖WithLp.ofLp x‖ = r} :=
    { toFun := f
      invFun := g
      left_inv := fun θ => Subtype.ext ((cube_radial_projection_inverse hr).1 θ).2
      right_inv := fun x => Subtype.ext ((cube_radial_projection_inverse hr).2 x)
      continuous_toFun := hf.continuous
      continuous_invFun := hg.continuous }
  exact ⟨H, fun _ => rfl, fun _ => rfl, hf, hg⟩

/-- The radial cube coordinates have constants independent of the radius on
the interval used for the cube-boundary selection. -/
theorem exists_cube_radial_bilipschitz_homeomorph_uniform {n : ℕ} {r : ℝ}
    (hrlo : (1 : ℝ) / 8 ≤ r) (hrhi : r ≤ (1 : ℝ) / 4) :
    ∃ H : sphere (0 : Domain n) 1 ≃ₜ {x : Domain n // ‖WithLp.ofLp x‖ = r},
      (∀ θ, (H θ).val = (r / ‖WithLp.ofLp θ.val‖) • θ.val) ∧
      (∀ x, (H.symm x).val = NormedSpace.normalize x.val) ∧
      LipschitzWith (Real.toNNReal (((n : ℝ) + (n : ℝ) ^ 2) / 4)) H ∧
      LipschitzWith 16 H.symm := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hrlo
  obtain ⟨H, hH, hHi, hf, hg⟩ := exists_cube_radial_bilipschitz_homeomorph (n := n) hr
  refine ⟨H, hH, hHi, hf.weaken ?_, hg.weaken ?_⟩
  · apply Real.toNNReal_mono
    have hc : 0 ≤ (n : ℝ) + (n : ℝ) ^ 2 :=
      add_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    calc
      r * ((n : ℝ) + (n : ℝ) ^ 2) ≤ (1 / 4) * ((n : ℝ) + (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hrhi hc
      _ = _ := by ring
  · have hc : 2 / r ≤ 16 := by
      apply (div_le_iff₀ hr).mpr
      nlinarith
    simpa using Real.toNNReal_mono hc

end StratificationTheory
