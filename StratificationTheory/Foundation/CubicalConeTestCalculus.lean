module

public import StratificationTheory.Foundation.CylinderTimeTests

/-!
# Smooth tests in face-cone parameters

The physical parametrization (x,t) ↦ (t x,t) has the explicit spatial and
time chain rules needed to transform native distributional pairings.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace StratificationTheory

private theorem cone_spatial_basis (n : ℕ) (i : Fin n) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (EuclideanSpace.single (Fin.castAdd 1 i) (1 : ℝ)) =
        (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

private theorem cone_clm_apply_sum {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : Domain n →L[ℝ] E) (x : Domain n) :
    L x = ∑ i : Fin n, x i • L (EuclideanSpace.single i 1) := by
  have hrepr : (∑ i : Fin n, x i • EuclideanSpace.single i 1) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  calc
    L x = L (∑ i : Fin n, x i • EuclideanSpace.single i 1) := congrArg L hrepr.symm
    _ = _ := by simp only [map_sum, map_smul]

/-- The actual spatial pullback of a smooth physical test has its original
physical spatial derivative multiplied by the current dilation. -/
theorem coordinateDerivative_cone_test_spatial {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x : Domain n) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let ψ : Domain n → ℝ := fun z => φ (e.symm (t • z, EuclideanSpace.single (0 : Fin 1) t))
    let hψ : ContDiff ℝ ∞ ψ := hφ.comp (e.symm.contDiff.comp
      ((contDiff_const_smul t).prodMk contDiff_const))
    coordinateDerivative ψ hψ i x =
      t * coordinateDerivative φ hφ (Fin.castAdd 1 i)
        (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) := by
  intro e ψ hψ
  have hp := ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul t).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) (EuclideanSpace.single (0 : Fin 1) t) x)
  have he := e.symm.hasFDerivAt.comp x hp
  have hc := ((hφ.differentiable (by simp)
    (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))).hasFDerivAt).comp x he
  change HasFDerivAt (fun z => φ (e.symm (t • z, EuclideanSpace.single (0 : Fin 1) t))) _ x at hc
  change fderiv ℝ _ x (EuclideanSpace.single i 1) = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.id_apply, zero_apply]
  change fderiv ℝ φ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))
    (e.symm (t • EuclideanSpace.single i 1, 0)) = _
  have hb : e.symm (t • EuclideanSpace.single i (1 : ℝ), 0) =
      t • EuclideanSpace.single (Fin.castAdd 1 i) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, map_smul, cone_spatial_basis]
    simp only [Prod.smul_mk, smul_zero]
  rw [hb, map_smul]
  rfl

/-- The time pullback of a smooth physical test differentiates into the
original time column plus the spatial dilation field, with all original
physical coordinate indices retained. -/
theorem hasDerivAt_cone_test_time {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    HasDerivAt (fun r => φ (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)))
      ((∑ i : Fin n, x i * coordinateDerivative φ hφ (Fin.castAdd 1 i)
        (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) +
        coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1))
          (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) t := by
  intro e
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hsingle (r : ℝ) : τ.symm r = EuclideanSpace.single (0 : Fin 1) r := by
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [τ, PiLp.equivOfUnique]
  have htime : HasDerivAt (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r)
      (EuclideanSpace.single (0 : Fin 1) 1) t := by
    have ht := τ.symm.hasFDerivAt.hasDerivAt (x := t)
    change HasDerivAt (fun r : ℝ => τ.symm r) (τ.symm 1) t at ht
    simp_rw [hsingle] at ht
    exact ht
  have hspace : HasDerivAt (fun r : ℝ => r • x) x t := by
    have ht := (hasDerivAt_id t).smul_const x
    change HasDerivAt (fun r : ℝ => r • x) ((1 : ℝ) • x) t at ht
    rw [one_smul] at ht
    exact ht
  have he := e.symm.hasFDerivAt.comp_hasDerivAt t (hspace.prodMk htime)
  have hc := ((hφ.differentiable (by simp)
    (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))).hasFDerivAt).comp_hasDerivAt t he
  let y := e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)
  let L : Domain n →L[ℝ] ℝ := (fderiv ℝ φ y).comp
    (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Domain n) (Domain 1)))
  have hsp : fderiv ℝ φ y (e.symm (x, 0)) =
      ∑ i : Fin n, x i * coordinateDerivative φ hφ (Fin.castAdd 1 i) y := by
    have hsum := cone_clm_apply_sum L x
    have hb (i : Fin n) : e.symm (EuclideanSpace.single i (1 : ℝ), 0) =
        EuclideanSpace.single (Fin.castAdd 1 i) 1 := by
      apply e.injective
      rw [e.apply_symm_apply, cone_spatial_basis]
    change fderiv ℝ φ y (e.symm (x, 0)) =
      ∑ i : Fin n, x i • fderiv ℝ φ y (e.symm (EuclideanSpace.single i 1, 0)) at hsum
    simp_rw [hb, smul_eq_mul] at hsum
    exact hsum
  have htm : e.symm (0, EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =
      EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, finAddEquivProd_time_basis]
  have hvec : e.symm (x, EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =
      e.symm (x, 0) + e.symm (0, EuclideanSpace.single (0 : Fin 1) 1) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  change HasDerivAt (fun r => φ (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)))
    (fderiv ℝ φ y (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) t at hc
  rw [hvec, map_add, hsp, htm] at hc
  exact hc

/-- A nonzero fixed face dilation pulls every compactly supported physical
test back to a compactly supported face test. -/
theorem hasCompactSupport_cone_test_spatial {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hcφ : HasCompactSupport φ) {t : ℝ} (ht : t ≠ 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    HasCompactSupport (fun x : Domain n =>
      φ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) := by
  intro e
  let K := (fun y : Domain (n + 1) => t⁻¹ • (e y).1) '' tsupport φ
  have hK : IsCompact K := hcφ.image
    ((continuous_const_smul t⁻¹).comp (continuous_fst.comp e.continuous))
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro x hx
  refine ⟨e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t), ?_, ?_⟩
  · exact subset_tsupport φ hx
  · change t⁻¹ • (e (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))).1 = x
    rw [e.apply_symm_apply, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Actual physical support inside the inverse face coordinates places the
whole support of the fixed-dilation test inside that same original face. -/
theorem tsupport_cone_test_subset_face {n : ℕ} {S : Set (Domain n)}
    {φ : Domain (n + 1) → ℝ} {t : ℝ} (ht : t ≠ 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    tsupport φ ⊆ {y : Domain (n + 1) | ((e y).2 0)⁻¹ • (e y).1 ∈ S} →
      tsupport (fun x : Domain n =>
        φ (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) ⊆ S := by
  intro e hs x hx
  have hp := tsupport_comp_subset_preimage
    (f := fun x : Domain n => e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))
    φ (e.symm.continuous.comp ((continuous_const_smul t).prodMk continuous_const)) hx
  have h := hs hp
  simp only [mem_setOf_eq, e.apply_symm_apply, PiLp.single_apply, ite_true,
    smul_smul, inv_mul_cancel₀ ht, one_smul] at h
  exact h

end StratificationTheory
