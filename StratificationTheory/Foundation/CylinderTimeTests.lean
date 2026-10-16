module

public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import HarmonicMaps.Sobolev
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Time tests on actual Euclidean cylinders

Products of compact spatial and temporal test functions are genuine ambient
compact tests. Their last coordinate derivative is the original time
derivative, so actual ambient weak gradients give the corresponding time
distributional identity.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff
namespace StratificationTheory

/-- The actual last Euclidean basis vector has zero spatial block and unit time block. -/
theorem finAddEquivProd_time_basis (n : ℕ) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) (1 : ℝ)) =
        (0, EuclideanSpace.single (0 : Fin 1) 1) := by
  apply Prod.ext
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

/-- Separable spatial-time scalar tests are smooth, compactly supported,
and supported in the actual open cylinder supplied by their test supports. -/
theorem cylinder_separable_test_admissible {n : ℕ} (U : OpenDomain n)
    {a b : ℝ} {ψ : Domain n → ℝ} {φ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U.val)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ioo a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let η : Domain (n + 1) → ℝ := fun y => ψ (e y).1 * φ ((e y).2 0)
    ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b} := by
  intro e η
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let c := e.trans (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Domain n)) τ)
  have heval (y : Domain (n + 1)) : c y = ((e y).1, (e y).2 0) := rfl
  let K := c ⁻¹' (tsupport ψ ×ˢ tsupport φ)
  have hK : IsCompact K := c.toHomeomorph.isCompact_preimage.mpr (hcψ.prod hcφ)
  have hsupport : Function.support η ⊆ K := by
    intro y hy
    change η y ≠ 0 at hy
    have hprod : ψ (e y).1 ≠ 0 ∧ φ ((e y).2 0) ≠ 0 := mul_ne_zero_iff.mp hy
    change c y ∈ tsupport ψ ×ˢ tsupport φ
    rw [heval]
    exact ⟨subset_tsupport ψ hprod.1, subset_tsupport φ hprod.2⟩
  have hts : tsupport η ⊆ K := closure_minimal hsupport hK.isClosed
  have hη : ContDiff ℝ ∞ η :=
    (hψ.comp (contDiff_fst.comp e.contDiff)).mul
      (hφ.comp ((EuclideanSpace.proj (0 : Fin 1)).contDiff.comp
        (contDiff_snd.comp e.contDiff)))
  refine ⟨hη, hK.of_isClosed_subset isClosed_closure hts, ?_⟩
  intro y hy
  have hmem := hts hy
  change c y ∈ tsupport ψ ×ˢ tsupport φ at hmem
  rw [heval] at hmem
  exact ⟨hsψ hmem.1, hsφ hmem.2⟩

/-- The last ambient coordinate derivative of a separable test is its actual
scalar time derivative, with the spatial factor unchanged. -/
theorem coordinateDerivative_cylinder_separable_time {n : ℕ}
    {ψ : Domain n → ℝ} {φ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hφ : ContDiff ℝ ∞ φ) (y : Domain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let η : Domain (n + 1) → ℝ := fun x => ψ (e x).1 * φ ((e x).2 0)
    fderiv ℝ η y (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) =
      ψ (e y).1 * deriv φ ((e y).2 0) := by
  intro e η
  let A : Domain (n + 1) →L[ℝ] Domain n :=
    (ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap
  let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
  have hp := ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y A.hasFDerivAt
  have hq := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y T.hasFDerivAt
  have h := hp.mul hq
  change fderiv ℝ ((ψ ∘ A) * (φ ∘ T)) y _ = _
  rw [h.fderiv]
  have hAB : A (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) = 0 := by
    change (e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)).1 = 0
    rw [finAddEquivProd_time_basis]
  have hTB : T (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) = 1 := by
    change (e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)).2 0 = 1
    rw [finAddEquivProd_time_basis]
    simp
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, hAB, hTB, map_zero, smul_zero, add_zero]
  rfl

/-- Genuine ambient weak gradients supply the separable time distributional
identity on the entire open cylinder, with the original last weak column. -/
theorem HasWeakGradient.cylinder_separable_time_identity {n q : ℕ}
    (U : OpenDomain n) {a b : ℝ}
    {w : Domain (n + 1) → Ambient q} {Dw : Domain (n + 1) → Gradient (n + 1) q}
    (hw : HasWeakGradient
      ⟨{y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp
              (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)))⟩ w Dw)
    {ψ : Domain n → ℝ} {φ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U.val)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ioo a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∫ y in {x : Domain (n + 1) | (e x).1 ∈ U.val ∧ (e x).2 0 ∈ Ioo a b},
      (ψ (e y).1 * deriv φ ((e y).2 0)) • w y) =
      -(∫ y in {x : Domain (n + 1) | (e x).1 ∈ U.val ∧ (e x).2 0 ∈ Ioo a b},
        (ψ (e y).1 * φ ((e y).2 0)) • Dw y (Fin.natAdd n (0 : Fin 1))) := by
  intro e
  let η : Domain (n + 1) → ℝ := fun y => ψ (e y).1 * φ ((e y).2 0)
  obtain ⟨hη, hcη, hsη⟩ := cylinder_separable_test_admissible U hψ hcψ hsψ hφ hcφ hsφ
  have hid := hw.2.2 (Fin.natAdd n (0 : Fin 1)) η hη hcη hsη
  have hD (y : Domain (n + 1)) : coordinateDerivative η hη (Fin.natAdd n (0 : Fin 1)) y =
      ψ (e y).1 * deriv φ ((e y).2 0) :=
    coordinateDerivative_cylinder_separable_time hψ hφ y
  simp_rw [hD] at hid
  exact hid

end StratificationTheory
