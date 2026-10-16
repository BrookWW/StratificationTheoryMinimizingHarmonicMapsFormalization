module

public import StratificationTheory.Foundation.UnitIntervalEnergy

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal BigOperators

namespace StratificationTheory

/-- The positive interpolation between scale one and scale lambda has a
uniform positive lower bound on the unit parameter interval. -/
theorem min_scale_le_radial_parameter {l t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    min 1 l ≤ 1 + t * (l - 1) := by
  calc
    min 1 l = (1 - t) * min 1 l + t * min 1 l := by ring
    _ ≤ (1 - t) * 1 + t * l :=
      add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (min_le_right _ _) ht.1)
    _ = 1 + t * (l - 1) := by ring

/-- The squared difference between two values on the same ray is controlled
by the actual radial classical derivative, with its positive parameter weight. -/
theorem smooth_radial_segment_energy_bound {n q : ℕ}
    (a x : Domain n) {l : ℝ} (hl : 0 < l)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) :
    ‖f (a + l • (x - a)) - f x‖ ^ 2 ≤
      (l - 1) ^ 2 * (min 1 l)⁻¹ ^ 2 *
        ∫ t in Ioc (0 : ℝ) 1,
          ‖fderiv ℝ f (a + (1 + t * (l - 1)) • (x - a))
            ((1 + t * (l - 1)) • (x - a))‖ ^ 2 := by
  let c : ℝ → ℝ := fun t => 1 + t * (l - 1)
  let γ : ℝ → Domain n := fun t => a + c t • (x - a)
  let d : ℝ → Ambient q := fun t => fderiv ℝ f (γ t) ((l - 1) • (x - a))
  let g : ℝ → ℝ := fun t => ‖fderiv ℝ f (γ t) (c t • (x - a))‖ ^ 2
  have hA : 0 < min 1 l := lt_min zero_lt_one hl
  have hγ : Continuous γ := by dsimp [γ, c]; fun_prop
  have hd : Continuous d := by
    dsimp [d]
    exact ((hf.continuous_fderiv (by simp)).comp hγ).clm_apply continuous_const
  have hg : Continuous g := by
    dsimp [g]
    exact (((hf.continuous_fderiv (by simp)).comp hγ).clm_apply
      (by dsimp [c]; fun_prop)).norm.pow 2
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => f (γ t)) (d t) t := by
    intro t _ht
    have hc : HasDerivAt c (l - 1) t := by
      convert (hasDerivAt_const t (1 : ℝ)).add
        ((hasDerivAt_id t).mul_const (l - 1)) using 1 <;> first | rfl | simp only [zero_add, one_mul]
    have hγd : HasDerivAt γ ((l - 1) • (x - a)) t := by
      convert (hasDerivAt_const t a).add (hc.smul_const (x - a)) using 1 <;> first | rfl | simp only [zero_add]
    exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hγd
  have hbound := unit_interval_energy_bound hd.continuousOn hderiv
  have hγone : γ 1 = a + l • (x - a) := by
    have hc1 : c 1 = l := by dsimp [c]; ring
    change a + c 1 • (x - a) = _
    rw [hc1]
  have hγzero : γ 0 = x := by simp only [γ, c, zero_mul, add_zero, one_smul]; abel
  rw [hγone, hγzero] at hbound
  apply hbound.trans
  have hdi : IntegrableOn (fun t => ‖d t‖ ^ 2) (Ioc (0 : ℝ) 1) volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgi : IntegrableOn g (Ioc (0 : ℝ) 1) volume :=
    hg.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← integral_const_mul]
  apply integral_mono_ae hdi (hgi.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hct : 0 < c t := hA.trans_le (min_scale_le_radial_parameter ⟨ht.1.le, ht.2⟩)
  have hinv : (c t)⁻¹ ≤ (min 1 l)⁻¹ :=
    (inv_le_inv₀ hct hA).mpr (min_scale_le_radial_parameter ⟨ht.1.le, ht.2⟩)
  have heq : d t = ((l - 1) * (c t)⁻¹) • fderiv ℝ f (γ t) (c t • (x - a)) := by
    rw [map_smul, smul_smul]
    dsimp [d]
    rw [map_smul]
    congr 1
    field_simp
  rw [heq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hct.le) hinv 2) (sq_nonneg _)) (sq_nonneg _)

/-- The ray interpolation scale does not exceed the larger endpoint scale. -/
theorem radial_parameter_le_max_scale {l t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 + t * (l - 1) ≤ max 1 l := by
  calc
    1 + t * (l - 1) = (1 - t) * 1 + t * l := by ring
    _ ≤ (1 - t) * max 1 l + t * max 1 l :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
    _ = max 1 l := by ring


end StratificationTheory
