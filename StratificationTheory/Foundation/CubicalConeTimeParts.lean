module

public import StratificationTheory.Foundation.CubicalConeTestCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Polynomial time integration by parts in face-cone coordinates

Physical tests supported in the open time slab vanish at both boundary
times. Their actual pullbacks obey the weighted identity with the exact
dimension coefficient that cancels the spatial divergence terms.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace StratificationTheory

/-- A smooth scalar test vanishing at both endpoints has the exact weighted
time integration-by-parts identity for every natural volume exponent. -/
theorem integral_unit_weight_mul_deriv_eq (m : ℕ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) :
    (∫ t in Ioo (0 : ℝ) 1, t ^ m * deriv ψ t) =
      -((m : ℝ) * ∫ t in Ioo (0 : ℝ) 1, t ^ (m - 1) * ψ t) := by
  have hpow : ContDiff ℝ ∞ (fun t : ℝ => t ^ m) := contDiff_id.pow m
  have hpowAC := (hpow.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
    (a := (0 : ℝ)) (b := 1)
  have hψAC := (hψ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
    (a := (0 : ℝ)) (b := 1)
  have hparts := hpowAC.integral_mul_deriv_eq_deriv_mul hψAC
  rw [hψ0, hψ1, mul_zero, mul_zero, sub_self, zero_sub] at hparts
  simp_rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    deriv_pow_field, mul_assoc] at hparts
  rw [integral_const_mul] at hparts
  exact hparts

/-- Physical support in the actual open time slab makes the origin and
the entire cap plane zero values of the original physical test. -/
theorem cone_test_time_boundary_values {n : ℕ} {φ : Domain (n + 1) → ℝ} :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    tsupport φ ⊆ {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1} →
      φ 0 = 0 ∧ ∀ x : Domain n,
        φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) = 0 := by
  intro e hs
  constructor
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    have ht := hs h
    change (e (0 : Domain (n + 1))).2 0 ∈ Ioo (0 : ℝ) 1 at ht
    rw [map_zero] at ht
    exact (lt_irrefl (0 : ℝ)) ht.1
  · intro x
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have ht := hs h
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))).2 0 ∈ Ioo (0 : ℝ) 1 at ht
    rw [e.apply_symm_apply] at ht
    exact (lt_irrefl (1 : ℝ)) (by simpa only [PiLp.single_apply, ite_true] using ht.2)

/-- The actual physical spatial and time columns of a cone test satisfy the
weighted time identity before any Sobolev map or derivative witness is used. -/
theorem integral_cone_test_time_parts {n : ℕ} (m : ℕ)
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    tsupport φ ⊆ {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1} →
    ∀ x : Domain n,
      (∫ t in Ioo (0 : ℝ) 1, t ^ m *
        ((∑ i : Fin n, x i * coordinateDerivative φ hφ (Fin.castAdd 1 i)
          (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) +
          coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1))
            (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)))) =
        -((m : ℝ) * ∫ t in Ioo (0 : ℝ) 1, t ^ (m - 1) *
          φ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) := by
  intro e hs x
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hsingle (r : ℝ) : τ.symm r = EuclideanSpace.single (0 : Fin 1) r := by
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [τ, PiLp.equivOfUnique]
  have hsingleSmooth : ContDiff ℝ ∞ (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) := by
    have h := τ.symm.contDiff (n := (∞ : ℕ∞ω))
    change ContDiff ℝ ∞ (fun r : ℝ => τ.symm r) at h
    simp_rw [hsingle] at h
    exact h
  let ψ : ℝ → ℝ := fun t => φ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))
  have hψ : ContDiff ℝ ∞ ψ :=
    hφ.comp (e.symm.contDiff.comp ((contDiff_smul_const x).prodMk hsingleSmooth))
  have hb := cone_test_time_boundary_values hs
  have hψ0 : ψ 0 = 0 := by
    have hz : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = (0 : Domain 1) := by
      ext i
      simp
    have hp : e.symm ((0 : Domain n), EuclideanSpace.single (0 : Fin 1) (0 : ℝ)) = 0 := by
      rw [hz]
      exact map_zero e.symm
    simpa only [ψ, zero_smul, hp] using hb.1
  have hψ1 : ψ 1 = 0 := by simpa only [ψ, one_smul] using hb.2 x
  have hderiv (t : ℝ) : deriv ψ t =
      (∑ i : Fin n, x i * coordinateDerivative φ hφ (Fin.castAdd 1 i)
        (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) +
        coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1))
          (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) :=
    (hasDerivAt_cone_test_time hφ x t).deriv
  simpa only [hderiv] using integral_unit_weight_mul_deriv_eq m hψ hψ0 hψ1

end StratificationTheory
