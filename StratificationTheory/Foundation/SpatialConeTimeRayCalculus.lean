module

public import StratificationTheory.Foundation.SpatialConeTimeDifferential
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Exact spatial ray values and differential of the cone-time chart

Positive spatial dilations leave the independent time variable unchanged.
The Fréchet differential retains its reciprocal spatial-height factor and
the original time direction.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff BigOperators
namespace StratificationTheory

/-- The actual chart is constant on positive spatial rays, with no dilation
of the independent time coordinate. -/
theorem spatial_cone_time_coordinates_spatial_ray (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm (((e ((E y).1)).2 0)⁻¹ • (e ((E y).1)).1, (E y).2)
    ∀ y, F (E.symm (r • (E y).1, (E y).2)) = F y := by
  intro e E F y
  dsimp only [F]
  rw [E.apply_symm_apply, map_smul]
  apply congrArg e.symm
  apply Prod.ext
  · change ((r * (e ((E y).1)).2 0)⁻¹) • (r • (e ((E y).1)).1) = _
    rw [mul_inv_rev, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
  · rfl

/-- The actual Fréchet differential of the chart at every nonzero spatial
height, applied to an arbitrary original Euclidean direction. -/
theorem fderiv_spatial_cone_time_coordinates_apply (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let X : Domain (n + 1 + 1) → Domain n := fun y => (e ((E y).1)).1
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • X y, (E y).2)
    ∀ y, T y ≠ 0 → ∀ v,
      fderiv ℝ F y v =
        e.symm ((T y)⁻¹ • X v - (((T y) ^ 2)⁻¹ * T v) • X y, (E v).2) := by
  intro e E T X F y hy v
  let P : Domain (n + 1 + 1) →L[ℝ] Domain (n + 1) :=
    (ContinuousLinearMap.fst ℝ (Domain (n + 1)) (Domain 1)).comp E.toContinuousLinearMap
  let LX : Domain (n + 1 + 1) →L[ℝ] Domain n :=
    (ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).comp (e.toContinuousLinearMap.comp P)
  let LT : Domain (n + 1 + 1) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 1)).comp
      ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp (e.toContinuousLinearMap.comp P))
  let LI : Domain (n + 1 + 1) →L[ℝ] Domain 1 :=
    (ContinuousLinearMap.snd ℝ (Domain (n + 1)) (Domain 1)).comp E.toContinuousLinearMap
  have hInv := (hasDerivAt_inv hy).comp_hasFDerivAt y (LT.hasFDerivAt (x := y))
  have hProd := (hInv.smul (LX.hasFDerivAt (x := y))).prodMk (LI.hasFDerivAt (x := y))
  have hAll := e.symm.hasFDerivAt.comp y hProd
  change HasFDerivAt F _ y at hAll
  rw [hAll.fderiv]
  change e.symm ((T y)⁻¹ • X v + (-((T y) ^ 2)⁻¹ * T v) • X y, (E v).2) = _
  apply congrArg e.symm
  apply Prod.ext
  · rw [neg_mul, neg_smul, sub_eq_add_neg]
  · rfl

end StratificationTheory
