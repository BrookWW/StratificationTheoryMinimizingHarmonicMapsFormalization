module

public import StratificationTheory.Foundation.CylinderRadialDifferential
public import StratificationTheory.Foundation.CylinderTimeTests
public import StratificationTheory.Interpolation.CylinderLinearInterpolation

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff RealInnerProductSpace
namespace StratificationTheory

private theorem spatial_normalization_column {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (θ : sphere (0 : Domain n) 1) (i : Fin n) :
    let hx : ρ • θ.val ≠ 0 := by
      intro h
      have hN := congrArg norm h
      have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
      rw [norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one, norm_zero] at hN
      exact hρ.ne' hN
    normalizationDifferential ⟨ρ • θ.val, hx⟩ (EuclideanSpace.single i 1) =
      ρ⁻¹ • (EuclideanSpace.single i 1 - θ.val i • θ.val) := by
  intro hx
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hN : ‖ρ • θ.val‖ = ρ := by
    rw [norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one]
  simp only [normalizationDifferential, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hN,
    EuclideanSpace.inner_single_right, map_smul, one_mul, conj_trivial]
  simp only [smul_smul, smul_sub, smul_eq_mul]
  have hc : ρ⁻¹ ^ 3 * (ρ * θ.val i * ρ) = ρ⁻¹ * θ.val i := by field_simp
  rw [hc]

/-- The actual spatial radial chart has reciprocal-radius spatial columns
and the unchanged original time column, on every positive spatial ray. -/
theorem fderiv_native_spatial_radial_chart_columns {n : ℕ} {a b : ℝ}
    (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c : unitCylinder n a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let θ : sphere (0 : Domain n) 1 := ⟨(e c.val).1, c.property.1⟩
    let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    let x := e.symm (ρ • θ.val, (e c.val).2)
    (∀ i : Fin n, fderiv ℝ F x (EuclideanSpace.single (Fin.castAdd 1 i) 1) =
      e.symm ((r / ρ) • (EuclideanSpace.single i 1 - θ.val i • θ.val), 0)) ∧
    fderiv ℝ F x (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) =
      e.symm (0, EuclideanSpace.single (0 : Fin 1) 1) := by
  intro e θ F x
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hx0 : (e x).1 ≠ 0 := by
    change (e (e.symm (ρ • θ.val, (e c.val).2))).1 ≠ 0
    rw [e.apply_symm_apply]
    intro h
    have hN := congrArg norm h
    rw [norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one, norm_zero] at hN
    exact hρ.ne' hN
  let A := ((r • normalizationDifferential ⟨(e x).1, hx0⟩).comp
      ((ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)).prod
        ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
  have hFirst := (ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).hasFDerivAt.comp x e.hasFDerivAt
  have hN := (hasFDerivAt_normalization ⟨(e x).1, hx0⟩).comp x hFirst
  have hSecond := (ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).hasFDerivAt.comp x e.hasFDerivAt
  have hDeriv : HasFDerivAt F (e.symm.toContinuousLinearMap.comp A) x :=
    e.symm.hasFDerivAt.comp x ((hN.const_smul r).prodMk hSecond)
  rw [hDeriv.fderiv]
  constructor
  · intro i
    have hBasis : e (EuclideanSpace.single (Fin.castAdd 1 i) (1 : ℝ)) =
        (EuclideanSpace.single i 1, 0) := finAddEquivProd_spatial_basis n i
    change e.symm (r • normalizationDifferential ⟨(e x).1, hx0⟩
        (e (EuclideanSpace.single (Fin.castAdd 1 i) 1)).1,
      (e (EuclideanSpace.single (Fin.castAdd 1 i) 1)).2) = _
    rw [hBasis]
    have hX : (e x).1 = ρ • θ.val := by simp only [x, e.apply_symm_apply]
    simp only [hX]
    rw [spatial_normalization_column hρ θ i]
    simp only [smul_smul, div_eq_mul_inv]
  · have hBasis : e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) (1 : ℝ)) =
        (0, EuclideanSpace.single (0 : Fin 1) 1) := finAddEquivProd_time_basis n
    change e.symm (r • normalizationDifferential ⟨(e x).1, hx0⟩
        (e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)).1,
      (e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)).2) = _
    rw [hBasis]
    simp only [map_zero, smul_zero]

/-- Spatial radial normalization preserves the selected native point at
all positive radii and keeps the original independent time coordinate. -/
theorem native_spatial_radial_chart_ray_value {n : ℕ} {a b : ℝ}
    (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c : unitCylinder n a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    F (e.symm (ρ • (e c.val).1, (e c.val).2)) = e.symm (r • (e c.val).1, (e c.val).2) := by
  intro e F
  have hθ : ‖(e c.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp c.property.1
  have hNorm : ‖ρ • (e c.val).1‖ = ρ := by
    rw [norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one]
  simp only [F, e.apply_symm_apply, hNorm, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hρ.ne', mul_one]

end StratificationTheory
