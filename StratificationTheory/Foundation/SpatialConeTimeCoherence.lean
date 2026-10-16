module

public import StratificationTheory.Foundation.SpatialConeTimeColumns

/-!
# Coherent spatial rays for the actual cone-time gradient

The literal chain-rule family is homogeneous of degree minus one in every
spatial column and degree zero in the independent time column. Its spatial
radial contraction vanishes at each nonzero chart height.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff BigOperators
namespace StratificationTheory

/-- Spatial dilation gives the genuine reciprocal-radius columns of the
same chain-rule family, while leaving the original time column unchanged. -/
theorem spatial_cone_time_chain_columns_spatial_ray {n q : ℕ}
    (Dw : Domain (n + 1) → Gradient (n + 1) q) {r : ℝ} (hr : r ≠ 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let X : Domain (n + 1 + 1) → Domain n := fun y => (e ((E y).1)).1
    let ξ : Domain (n + 1 + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y => e.symm (ξ y, (E y).2)
    let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y i =>
      ∑ j : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Dw (F y) j
    ∀ y, T y ≠ 0 →
      let z := E.symm (r • (E y).1, (E y).2)
      (∀ i : Fin (n + 1), D z (Fin.castAdd 1 i) = r⁻¹ • D y (Fin.castAdd 1 i)) ∧
      D z (Fin.natAdd (n + 1) (0 : Fin 1)) = D y (Fin.natAdd (n + 1) (0 : Fin 1)) := by
  intro e E T X ξ F D y hy z
  have hT : T z = r * T y := by
    dsimp only [T, z]
    rw [E.apply_symm_apply, map_smul]
    rfl
  have hz : T z ≠ 0 := by rw [hT]; exact mul_ne_zero hr hy
  have hF : F z = F y := spatial_cone_time_coordinates_spatial_ray n hr y
  have hξ : ξ z = ξ y := by
    have h := congrArg (fun w => (e w).1) hF
    simpa only [F, e.apply_symm_apply] using h
  have hcolumns (p : Domain (n + 1 + 1)) (hp : T p ≠ 0) :
      (∀ i : Fin n, D p (Fin.castAdd 1 (Fin.castAdd 1 i)) =
        (T p)⁻¹ • Dw (F p) (Fin.castAdd 1 i)) ∧
      D p (Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1))) =
        -((T p)⁻¹ • ∑ i : Fin n, ξ p i • Dw (F p) (Fin.castAdd 1 i)) ∧
      D p (Fin.natAdd (n + 1) (0 : Fin 1)) = Dw (F p) (Fin.natAdd n (0 : Fin 1)) :=
    spatial_cone_time_chain_columns Dw p hp
  obtain ⟨hs, hh, ht⟩ := hcolumns y hy
  obtain ⟨hsz, hhz, htz⟩ := hcolumns z hz
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hsz, hs, hT, hF, mul_inv_rev, mul_comm (T y)⁻¹ r⁻¹, mul_smul]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [hhz, hh, hT, hF, hξ, mul_inv_rev, mul_comm (T y)⁻¹ r⁻¹,
        mul_smul, smul_neg]
  · rw [htz, ht, hF]

/-- The actual spatial columns annihilate the actual spatial radial vector. -/
theorem spatial_cone_time_chain_columns_radial_tangent {n q : ℕ}
    (Dw : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let X : Domain (n + 1 + 1) → Domain n := fun y => (e ((E y).1)).1
    let ξ : Domain (n + 1 + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y => e.symm (ξ y, (E y).2)
    let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y i =>
      ∑ j : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Dw (F y) j
    ∀ y, T y ≠ 0 → ∑ i : Fin (n + 1), (E y).1 i • D y (Fin.castAdd 1 i) = 0 := by
  intro e E T X ξ F D y hy
  have hcolumns :
      (∀ i : Fin n, D y (Fin.castAdd 1 (Fin.castAdd 1 i)) =
        (T y)⁻¹ • Dw (F y) (Fin.castAdd 1 i)) ∧
      D y (Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1))) =
        -((T y)⁻¹ • ∑ i : Fin n, ξ y i • Dw (F y) (Fin.castAdd 1 i)) ∧
      D y (Fin.natAdd (n + 1) (0 : Fin 1)) = Dw (F y) (Fin.natAdd n (0 : Fin 1)) :=
    spatial_cone_time_chain_columns Dw y hy
  obtain ⟨hs, hh, _⟩ := hcolumns
  have hx (i : Fin n) : (E y).1 (Fin.castAdd 1 i) = X y i := rfl
  have ht : (E y).1 (Fin.natAdd n (0 : Fin 1)) = T y := rfl
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [hx, ht, hs, hh, smul_neg, smul_smul, mul_inv_cancel₀ hy, one_smul]
  have hsum : (∑ i : Fin n, X y i • (T y)⁻¹ • Dw (F y) (Fin.castAdd 1 i)) =
      ∑ i : Fin n, ξ y i • Dw (F y) (Fin.castAdd 1 i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    change (X y i * (T y)⁻¹) • _ = ((T y)⁻¹ * X y i) • _
    rw [mul_comm]
  simp only [smul_smul] at hsum
  rw [hsum, add_neg_cancel]

end StratificationTheory
