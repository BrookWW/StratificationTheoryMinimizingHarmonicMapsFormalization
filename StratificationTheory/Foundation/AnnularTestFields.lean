module

public import StratificationTheory.Foundation.SphericalProjectionDifferential
public import StratificationTheory.Foundation.CylinderCoordinateMeasure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import HarmonicMaps.Analysis.RadialVectorField

/-!
# Compact annular change-of-variables test fields

The spatial tangential and temporal radial components carry the actual
annular Jacobian. Their coordinate divergence cancels its derivative exactly.
Compact radial and temporal cutoffs produce globally smooth admissible
Euclidean weak-gradient tests supported in the original cylinder collar.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ContDiff BigOperators
namespace StratificationTheory

/-- The spatial tangential test field in the actual radial change of variables. -/
@[expose] noncomputable def annularSpatialTestField {n : ℕ}
    (L : ℝ) (β : ℝ → ℝ) (ψ : Domain n → ℝ) (i : Fin n) (x : Domain n) : Domain n :=
  let θ := ‖x‖⁻¹ • x
  (β ‖x‖ * ψ (L • θ)) • (‖x‖ • EuclideanSpace.single i 1 - θ i • x)

/-- The actual spatial-time field carries the radial annulus Jacobian and
its tangential spatial and radial temporal components. -/
@[expose] noncomputable def annularTestField {n : ℕ} (s : ℝ)
    (β ζ : ℝ → ℝ) (ψ : Domain n → ℝ) (i : Fin n)
    (y : Domain (n + 1)) : Domain (n + 1) :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let x := (e y).1
  let t := (e y).2 0
  let L := s * (1 + t)
  let θ := ‖x‖⁻¹ • x
  e.symm ((s * L ^ (n - 2) * ζ t) • annularSpatialTestField L β ψ i x,
    EuclideanSpace.single (0 : Fin 1)
      (L ^ (n - 1) * β ‖x‖ * ζ t * ψ (L • θ) * θ i))

/-- Away from the actual spatial origin all components of the annular test
field are smooth functions of the original Euclidean spatial-time variables. -/
theorem contDiffOn_annularTestField_punctured {n : ℕ} (s : ℝ)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ContDiffOn ℝ ∞ (annularTestField s β ζ ψ i)
      {y : Domain (n + 1) | (e y).1 ≠ 0} := by
  intro e
  let U := {y : Domain (n + 1) | (e y).1 ≠ 0}
  have hx : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) => (e y).1) U :=
    (contDiff_fst.comp e.contDiff).contDiffOn
  have ht : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) => (e y).2 0) U :=
    ((EuclideanSpace.proj (0 : Fin 1)).contDiff.comp (contDiff_snd.comp e.contDiff)).contDiffOn
  have hr : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) => ‖(e y).1‖) U :=
    hx.norm ℝ (fun y hy => hy)
  have hθ : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) => ‖(e y).1‖⁻¹ • (e y).1) U :=
    contDiffOn_normalization.comp hx (fun y hy => hy)
  have hθi : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) => (‖(e y).1‖⁻¹ • (e y).1) i) U :=
    by
      have hp : ContDiff ℝ ∞ (fun z : Domain n => z i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
      exact hp.comp_contDiffOn hθ
  have hL : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) => s * (1 + (e y).2 0)) U :=
    contDiffOn_const.mul (contDiffOn_const.add ht)
  have hψc := hψ.comp_contDiffOn (hL.smul hθ)
  have hβc := hβ.comp_contDiffOn hr
  have hζc := hζ.comp_contDiffOn ht
  have hZ : ContDiffOn ℝ ∞ (fun y : Domain (n + 1) =>
      ‖(e y).1‖ • EuclideanSpace.single i 1 - (‖(e y).1‖⁻¹ • (e y).1) i • (e y).1) U :=
    (hr.smul contDiffOn_const).sub (hθi.smul hx)
  have hs : ContDiffOn ℝ ∞ (fun _ : Domain (n + 1) => s) U := contDiffOn_const
  have hspace := ((hs.mul (hL.pow (n - 2))).mul hζc).smul
    ((hβc.mul hψc).smul hZ)
  have htime := ((((hL.pow (n - 1)).mul hβc).mul hζc).mul hψc).mul hθi
  have hsingle : ContDiff ℝ ∞ (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    apply (contDiff_piLp 2).mpr
    intro j
    simp only [EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp, Pi.single_apply]
    split_ifs <;> first | exact contDiff_id | exact contDiff_const
  exact e.symm.contDiff.comp_contDiffOn (hspace.prodMk (hsingle.comp_contDiffOn htime))

/-- A radial cutoff supported away from zero removes the spatial singularity
and makes the actual annular test field globally smooth. -/
theorem contDiff_annularTestField {n : ℕ} (s : ℝ)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hβ0 : (0 : ℝ) ∉ tsupport β) (i : Fin n) :
    ContDiff ℝ ∞ (annularTestField s β ζ ψ i) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : (e y).1 = 0
  · have hnb : ∀ᶠ z in 𝓝 y, ‖(e z).1‖ ∉ tsupport β := by
      have hcont : Continuous (fun z : Domain (n + 1) => ‖(e z).1‖) :=
        e.continuous.fst.norm
      have hzero : ‖(e y).1‖ ∈ (tsupport β)ᶜ := by
        simpa only [hy, norm_zero, mem_compl_iff] using hβ0
      exact hcont.continuousAt ((isClosed_tsupport β).isOpen_compl.mem_nhds hzero)
    have heq : annularTestField s β ζ ψ i =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hnb] with z hz
      have hbz := image_eq_zero_of_notMem_tsupport hz
      dsimp only [e] at hbz
      have hsingle0 : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = (0 : Domain 1) := by
        ext j
        simp only [EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp, Pi.single_zero,
          Pi.zero_apply, PiLp.zero_apply]
      simp only [annularTestField, annularSpatialTestField, hbz, zero_mul, zero_smul,
        mul_zero, smul_zero, hsingle0, ← Prod.zero_eq_mk, map_zero]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hU : IsOpen {z : Domain (n + 1) | (e z).1 ≠ 0} :=
      (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (Domain n))).preimage e.continuous.fst
    exact (contDiffOn_annularTestField_punctured s hβ hζ hψ i).contDiffAt
      (hU.mem_nhds hy)


private theorem annularTestField_eq_zero_of_cutoff {n : ℕ} (s : ℝ)
    (β ζ : ℝ → ℝ) (ψ : Domain n → ℝ) (i : Fin n) (y : Domain (n + 1))
    (hzero : β ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ = 0 ∨
      ζ ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0) = 0) :
    annularTestField s β ζ ψ i y = 0 := by
  have hsingle0 : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = (0 : Domain 1) := by
    ext j
    simp only [EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp, Pi.single_zero,
      Pi.zero_apply, PiLp.zero_apply]
  rcases hzero with hzero | hzero <;>
    simp only [annularTestField, annularSpatialTestField, hzero, zero_mul, mul_zero,
      zero_smul, smul_zero, hsingle0, ← Prod.zero_eq_mk, map_zero]

/-- Compact radial and temporal cutoffs give a genuinely compactly supported
ambient Euclidean test field; no compactness of the annular test is assumed. -/
theorem hasCompactSupport_annularTestField {n : ℕ} (s : ℝ)
    {β ζ : ℝ → ℝ} (hβ : HasCompactSupport β) (hζ : HasCompactSupport ζ)
    (ψ : Domain n → ℝ) (i : Fin n) :
    HasCompactSupport (annularTestField s β ζ ψ i) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let C := e.trans (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Domain n)) τ)
  obtain ⟨R, hR⟩ := hβ.exists_bound_of_continuousOn (f := fun r : ℝ => r) continuousOn_id
  let K := C ⁻¹' (closedBall (0 : Domain n) R ×ˢ tsupport ζ)
  have hK : IsCompact K := C.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall (0 : Domain n) R).prod hζ)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro y hy
  have hβy : β ‖(e y).1‖ ≠ 0 := by
    intro hz
    exact hy (annularTestField_eq_zero_of_cutoff s β ζ ψ i y (Or.inl hz))
  have hζy : ζ ((e y).2 0) ≠ 0 := by
    intro hz
    exact hy (annularTestField_eq_zero_of_cutoff s β ζ ψ i y (Or.inr hz))
  have hRbound := hR ‖(e y).1‖ (subset_tsupport β hβy)
  change (C y).1 ∈ closedBall (0 : Domain n) R ∧ (C y).2 ∈ tsupport ζ
  refine ⟨?_, subset_tsupport ζ hζy⟩
  change (e y).1 ∈ closedBall (0 : Domain n) R
  rw [mem_closedBall, dist_zero_right]
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hRbound

/-- Both cutoff supports place the entire test support in the original open
spatial collar times the original open time interval. -/
theorem tsupport_annularTestField_subset_collar {n : ℕ} (s : ℝ)
    {β ζ : ℝ → ℝ}
    {l r a b : ℝ} (hβsupport : tsupport β ⊆ Ioo l r)
    (hζsupport : tsupport ζ ⊆ Ioo a b) (ψ : Domain n → ℝ) (i : Fin n) :
    tsupport (annularTestField s β ζ ψ i) ⊆
      {y : Domain (n + 1) |
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∈ Ioo l r ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  have hs : Function.support (annularTestField s β ζ ψ i) ⊆
      {y : Domain (n + 1) | ‖(e y).1‖ ∈ tsupport β ∧ (e y).2 0 ∈ tsupport ζ} := by
    intro y hy
    constructor
    · apply subset_tsupport β
      intro hz
      exact hy (annularTestField_eq_zero_of_cutoff s β ζ ψ i y (Or.inl hz))
    · apply subset_tsupport ζ
      intro hz
      exact hy (annularTestField_eq_zero_of_cutoff s β ζ ψ i y (Or.inr hz))
  have hc : IsClosed {y : Domain (n + 1) | ‖(e y).1‖ ∈ tsupport β ∧
      (e y).2 0 ∈ tsupport ζ} :=
    ((isClosed_tsupport β).preimage e.continuous.fst.norm).inter
      ((isClosed_tsupport ζ).preimage
        ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp e.continuous.snd))
  have hts := closure_minimal hs hc
  intro y hy
  exact ⟨hβsupport (hts hy).1, hζsupport (hts hy).2⟩


/-- The actual spatial test field has the full chain-rule derivative, with
the radial and normalization differentials on their original carriers. -/
theorem fderiv_annularSpatialTestField {n : ℕ} (L : ℝ)
    {β : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Domain n) (hx : x ≠ 0) (v : Domain n) :
    let θ := ‖x‖⁻¹ • x
    let D := normalizationDifferential ⟨x, hx⟩
    fderiv ℝ (annularSpatialTestField L β ψ i) x v =
      (deriv β ‖x‖ * (‖x‖⁻¹ * inner ℝ x v) * ψ (L • θ) +
        β ‖x‖ * fderiv ℝ ψ (L • θ) (L • D v)) •
          (‖x‖ • EuclideanSpace.single i 1 - θ i • x) +
      (β ‖x‖ * ψ (L • θ)) •
        ((‖x‖⁻¹ * inner ℝ x v) • EuclideanSpace.single i 1 - (D v) i • x - θ i • v) := by
  intro θ D
  have hr := radialNorm_hasFDerivAt hx
  have hθ := hasFDerivAt_normalization ⟨x, hx⟩
  have hθi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hθ
  have hA := (hβ.differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x hr
  have hB := (hψ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    (hθ.const_smul L)
  have hZ := (hr.smul (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)).sub
    (hθi.smul (hasFDerivAt_id x))
  have hfield := (hA.mul hB).smul hZ
  change HasFDerivAt (annularSpatialTestField L β ψ i) _ x at hfield
  rw [hfield.fderiv]
  change
    (β ‖x‖ * ψ (L • θ)) •
      ((‖x‖ • 0 + (‖x‖⁻¹ * inner ℝ x v) • EuclideanSpace.single i 1) -
        (θ i • v + (D v) i • x)) +
    (β ‖x‖ * fderiv ℝ ψ (L • θ) (L • D v) +
      ψ (L • θ) * (deriv β ‖x‖ * (‖x‖⁻¹ * inner ℝ x v))) •
        (‖x‖ • EuclideanSpace.single i 1 - θ i • x) = _
  rw [smul_zero, zero_add]
  have hcoeff : β ‖x‖ * fderiv ℝ ψ (L • θ) (L • D v) +
      ψ (L • θ) * (deriv β ‖x‖ * (‖x‖⁻¹ * inner ℝ x v)) =
      deriv β ‖x‖ * (‖x‖⁻¹ * inner ℝ x v) * ψ (L • θ) +
        β ‖x‖ * fderiv ℝ ψ (L • θ) (L • D v) := by ring
  rw [hcoeff, sub_add_eq_sub_sub]
  abel_nf


private theorem normalizationDifferential_radial_zero {n : ℕ}
    (x : {x : Domain n // x ≠ 0}) : normalizationDifferential x x.val = 0 := by
  change ‖x.val‖⁻¹ • x.val - (‖x.val‖⁻¹ ^ 3) • (inner ℝ x.val x.val • x.val) = 0
  rw [real_inner_self_eq_norm_sq, smul_smul, ← sub_smul]
  have hnorm : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
  have hcoeff : ‖x.val‖⁻¹ - ‖x.val‖⁻¹ ^ 3 * ‖x.val‖ ^ 2 = 0 := by
    field_simp
    ring
  rw [hcoeff, zero_smul]

private theorem normalizationDifferential_tangential_vector {n : ℕ}
    (x : {x : Domain n // x ≠ 0}) (i : Fin n) :
    let θ := ‖x.val‖⁻¹ • x.val
    normalizationDifferential x (‖x.val‖ • EuclideanSpace.single i 1 - θ i • x.val) =
      EuclideanSpace.single i 1 - θ i • θ := by
  intro θ
  rw [map_sub, map_smul, map_smul, normalizationDifferential_radial_zero, smul_zero, sub_zero]
  change ‖x.val‖ • (‖x.val‖⁻¹ • EuclideanSpace.single i 1 -
    (‖x.val‖⁻¹ ^ 3) • (inner ℝ x.val (EuclideanSpace.single i 1) • x.val)) = _
  rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul, smul_sub, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property), one_smul, smul_smul]
  rw [smul_smul]
  change EuclideanSpace.single i 1 - ((‖x.val‖ * ‖x.val‖⁻¹ ^ 3) * x.val i) • x.val =
    EuclideanSpace.single i 1 - (‖x.val‖⁻¹ * x.val i) • (‖x.val‖⁻¹ • x.val)
  rw [smul_smul]
  congr 2
  field_simp

private theorem annular_radius_tangential_vector {n : ℕ}
    (x : {x : Domain n // x ≠ 0}) (i : Fin n) :
    let θ := ‖x.val‖⁻¹ • x.val
    ‖x.val‖⁻¹ * inner ℝ x.val
      (‖x.val‖ • EuclideanSpace.single i 1 - θ i • x.val) = 0 := by
  intro θ
  rw [inner_sub_right, inner_smul_right, inner_smul_right,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, real_inner_self_eq_norm_sq]
  change ‖x.val‖⁻¹ * (‖x.val‖ * x.val i - (‖x.val‖⁻¹ * x.val i) * ‖x.val‖ ^ 2) = 0
  field_simp
  ring

private theorem sum_scalar_map_basis_mul_coordinate {n : ℕ}
    (A : Domain n →L[ℝ] ℝ) (z : Domain n) :
    (∑ j : Fin n, A (EuclideanSpace.single j 1) * z j) = A z := by
  have hrepr : (∑ j : Fin n, z j • EuclideanSpace.single j 1) = z := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
  calc
    _ = A (∑ j : Fin n, z j • EuclideanSpace.single j 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = A z := congrArg A hrepr


/-- The exact spatial divergence separates the desired annular derivative
from its radial and dimension terms. Radial-cutoff derivatives cancel. -/
theorem divergence_annularSpatialTestField {n : ℕ} (L : ℝ)
    {β : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Domain n) (hx : x ≠ 0) :
    let θ := ‖x‖⁻¹ • x
    (∑ j : Fin n,
      (fderiv ℝ (annularSpatialTestField L β ψ i) x (EuclideanSpace.single j 1)) j) =
      β ‖x‖ * (L * coordinateDerivative ψ hψ i (L • θ) -
        L * θ i * fderiv ℝ ψ (L • θ) θ - ((n : ℝ) - 1) * θ i * ψ (L • θ)) := by
  intro θ
  let D := normalizationDifferential ⟨x, hx⟩
  let dr : Domain n →L[ℝ] ℝ := ‖x‖⁻¹ • innerSL ℝ x
  let Z := ‖x‖ • EuclideanSpace.single i 1 - θ i • x
  let A : Domain n →L[ℝ] ℝ :=
    (deriv β ‖x‖ * ψ (L • θ)) • dr +
      β ‖x‖ • (fderiv ℝ ψ (L • θ)).comp (L • D)
  have hA (v : Domain n) : A v =
      deriv β ‖x‖ * (‖x‖⁻¹ * inner ℝ x v) * ψ (L • θ) +
        β ‖x‖ * fderiv ℝ ψ (L • θ) (L • D v) := by
    change (deriv β ‖x‖ * ψ (L • θ)) * (‖x‖⁻¹ * inner ℝ x v) +
      β ‖x‖ * fderiv ℝ ψ (L • θ) (L • D v) = _
    ring
  have hjj (j : Fin n) : (EuclideanSpace.single j (1 : ℝ)) j = 1 := by
    simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
  have hcol (j : Fin n) :
      (fderiv ℝ (annularSpatialTestField L β ψ i) x (EuclideanSpace.single j 1)) j =
      A (EuclideanSpace.single j 1) * Z j + (β ‖x‖ * ψ (L • θ)) *
        (dr (EuclideanSpace.single j 1) * (EuclideanSpace.single i 1) j -
          (D (EuclideanSpace.single j 1)) i * x j - θ i) := by
    rw [fderiv_annularSpatialTestField L hβ hψ i x hx (EuclideanSpace.single j 1), hA]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hjj, mul_one]
    rfl
  have hfirst : (∑ j : Fin n,
      dr (EuclideanSpace.single j 1) * (EuclideanSpace.single i 1) j) = θ i := by
    rw [sum_scalar_map_basis_mul_coordinate]
    change ‖x‖⁻¹ * inner ℝ x (EuclideanSpace.single i 1) = θ i
    rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    rfl
  have hsecond : (∑ j : Fin n, (D (EuclideanSpace.single j 1)) i * x j) = 0 := by
    have hsum := sum_scalar_map_basis_mul_coordinate
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp D) x
    change (∑ j : Fin n, (D (EuclideanSpace.single j 1)) i * x j) = (D x) i at hsum
    rw [hsum, normalizationDifferential_radial_zero]
    rfl
  have hdivZ : (∑ j : Fin n,
      (dr (EuclideanSpace.single j 1) * (EuclideanSpace.single i 1) j -
        (D (EuclideanSpace.single j 1)) i * x j - θ i)) =
      (1 - (n : ℝ)) * θ i := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hfirst, hsecond,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hAZ : A Z = β ‖x‖ * L *
      (coordinateDerivative ψ hψ i (L • θ) - θ i * fderiv ℝ ψ (L • θ) θ) := by
    rw [hA, annular_radius_tangential_vector ⟨x, hx⟩ i,
      normalizationDifferential_tangential_vector ⟨x, hx⟩ i]
    rw [mul_zero, zero_mul, zero_add, map_smul, map_sub, map_smul]
    change β ‖x‖ * (L * (coordinateDerivative ψ hψ i (L • θ) -
      θ i * fderiv ℝ ψ (L • θ) θ)) = _
    ring
  calc
    _ = (∑ j : Fin n, A (EuclideanSpace.single j 1) * Z j) +
        (β ‖x‖ * ψ (L • θ)) * (∑ j : Fin n,
          (dr (EuclideanSpace.single j 1) * (EuclideanSpace.single i 1) j -
            (D (EuclideanSpace.single j 1)) i * x j - θ i)) := by
      simp_rw [hcol]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [sum_scalar_map_basis_mul_coordinate, hAZ, hdivZ]
      ring


private theorem differentiableAt_annularSpatialTestField {n : ℕ} (L : ℝ)
    {β : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Domain n) (hx : x ≠ 0) :
    DifferentiableAt ℝ (annularSpatialTestField L β ψ i) x := by
  have hr := (radialNorm_hasFDerivAt hx).differentiableAt
  have hθ := (hasFDerivAt_normalization ⟨x, hx⟩).differentiableAt
  have hθi := (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x hθ
  have hA := (hβ.differentiable (by simp)).differentiableAt.comp x hr
  have hB := (hψ.differentiable (by simp)).differentiableAt.comp x (hθ.const_smul L)
  exact (hA.mul hB).smul ((hr.smul (differentiableAt_const (EuclideanSpace.single i (1 : ℝ)))).sub
    (hθi.smul differentiableAt_id))

/-- The temporal Jacobian component has its actual derivative, including the
time-cutoff term needed before compact annular tests remove that term. -/
theorem deriv_annularTestField_time_component {n : ℕ} (hn : 2 ≤ n) (s : ℝ)
    (β : ℝ → ℝ) {ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Domain n) (t : ℝ) :
    let θ := ‖x‖⁻¹ • x
    let L := s * (1 + t)
    deriv (fun τ : ℝ => (s * (1 + τ)) ^ (n - 1) * β ‖x‖ * ζ τ *
      ψ ((s * (1 + τ)) • θ) * θ i) t =
      ((n - 1 : ℕ) : ℝ) * s * L ^ (n - 2) * β ‖x‖ * ζ t * ψ (L • θ) * θ i +
      L ^ (n - 1) * β ‖x‖ * deriv ζ t * ψ (L • θ) * θ i +
      s * L ^ (n - 1) * β ‖x‖ * ζ t * fderiv ℝ ψ (L • θ) θ * θ i := by
  intro θ L
  have hL : HasDerivAt (fun τ : ℝ => s * (1 + τ)) s t := by
    convert ((hasDerivAt_id t).const_add 1).const_mul s using 1 <;>
      first | rfl | ring
  have hζt := (hζ.differentiable (by simp)).differentiableAt.hasDerivAt (x := t)
  have hψt := (hψ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (hL.smul_const θ)
  have htotal := ((((hL.pow (n - 1)).mul (hasDerivAt_const t (β ‖x‖))).mul hζt).mul hψt).mul
    (hasDerivAt_const t (θ i))
  change HasDerivAt (fun τ : ℝ => (s * (1 + τ)) ^ (n - 1) * β ‖x‖ * ζ τ *
    ψ ((s * (1 + τ)) • θ) * θ i) _ t at htotal
  rw [htotal.deriv]
  have hindex : n - 1 - 1 = n - 2 := by omega
  rw [hindex, map_smul]
  dsimp only [L, Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
  ring

/-- The spatial and temporal coordinate divergences of the actual annular
test field cancel the Jacobian derivative exactly. -/
theorem annularTestField_split_divergence {n : ℕ} (hn : 2 ≤ n) (s : ℝ)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Domain n) (hx : x ≠ 0) (t : ℝ) :
    let θ := ‖x‖⁻¹ • x
    let L := s * (1 + t)
    (∑ j : Fin n, (fderiv ℝ (fun z : Domain n =>
      (s * L ^ (n - 2) * ζ t) • annularSpatialTestField L β ψ i z) x
        (EuclideanSpace.single j 1)) j) +
      deriv (fun τ : ℝ => (s * (1 + τ)) ^ (n - 1) * β ‖x‖ * ζ τ *
        ψ ((s * (1 + τ)) • θ) * θ i) t =
      s * L ^ (n - 1) * β ‖x‖ * ζ t * coordinateDerivative ψ hψ i (L • θ) +
        L ^ (n - 1) * β ‖x‖ * deriv ζ t * ψ (L • θ) * θ i := by
  intro θ L
  have hX := (differentiableAt_annularSpatialTestField L hβ hψ i x hx).hasFDerivAt.const_smul
    (s * L ^ (n - 2) * ζ t)
  change HasFDerivAt (fun z : Domain n =>
    (s * L ^ (n - 2) * ζ t) • annularSpatialTestField L β ψ i z) _ x at hX
  rw [hX.fderiv, deriv_annularTestField_time_component hn s β hζ hψ i x t]
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, divergence_annularSpatialTestField L hβ hψ i x hx]
  have hindex : n - 1 = n - 2 + 1 := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hcast, hindex, pow_succ]
  dsimp only [L, θ]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring


/-- The physical Euclidean test field has precisely the two displayed
components under the canonical spatial-time coordinate equivalence. -/
theorem annularTestField_coordinates {n : ℕ} (s : ℝ)
    (β ζ : ℝ → ℝ) (ψ : Domain n → ℝ) (i : Fin n) (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let θ := ‖x‖⁻¹ • x
    let L := s * (1 + t)
    e (annularTestField s β ζ ψ i
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) =
      ((s * L ^ (n - 2) * ζ t) • annularSpatialTestField L β ψ i x,
        EuclideanSpace.single (0 : Fin 1)
          (L ^ (n - 1) * β ‖x‖ * ζ t * ψ (L • θ) * θ i)) := by
  intro e θ L
  dsimp only [e, θ, L]
  simp only [annularTestField, ContinuousLinearEquiv.apply_symm_apply, EuclideanSpace.single,
    PiLp.single_apply, ite_true]

/-- The divergence computed from the actual physical field's spatial and
temporal coordinate functions has the exact annular Jacobian formula. -/
theorem annularTestField_coordinate_divergence {n : ℕ} (hn : 2 ≤ n) (s : ℝ)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Domain n) (hx : x ≠ 0) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let θ := ‖x‖⁻¹ • x
    let L := s * (1 + t)
    (∑ j : Fin n, (fderiv ℝ (fun z : Domain n =>
      (e (annularTestField s β ζ ψ i
        (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).1) x
          (EuclideanSpace.single j 1)) j) +
      deriv (fun τ : ℝ => (e (annularTestField s β ζ ψ i
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ)))).2 0) t =
      s * L ^ (n - 1) * β ‖x‖ * ζ t * coordinateDerivative ψ hψ i (L • θ) +
        L ^ (n - 1) * β ‖x‖ * deriv ζ t * ψ (L • θ) * θ i := by
  intro e θ L
  have hspatial : (fun z : Domain n => (e (annularTestField s β ζ ψ i
      (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).1) =
      (fun z : Domain n => (s * L ^ (n - 2) * ζ t) • annularSpatialTestField L β ψ i z) := by
    funext z
    exact congrArg Prod.fst (annularTestField_coordinates s β ζ ψ i z t)
  have htime : (fun τ : ℝ => (e (annularTestField s β ζ ψ i
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ)))).2 0) =
      (fun τ : ℝ => (s * (1 + τ)) ^ (n - 1) * β ‖x‖ * ζ τ *
        ψ ((s * (1 + τ)) • θ) * θ i) := by
    funext τ
    have h := congrArg (fun p : Domain n × Domain 1 => p.2 0)
      (annularTestField_coordinates s β ζ ψ i x τ)
    simpa only [EuclideanSpace.single, PiLp.single_apply, ite_true] using h
  rw [hspatial, htime]
  exact annularTestField_split_divergence hn s hβ hζ hψ i x hx t


/-- Every actual Euclidean component is an admissible scalar weak-gradient
test on the original radial collar and time interval. -/
theorem annularTestField_component_admissible {n : ℕ} (s : ℝ)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hcβ : HasCompactSupport β) (hcζ : HasCompactSupport ζ)
    {l r a b : ℝ} (hl : 0 ≤ l) (hsβ : tsupport β ⊆ Ioo l r)
    (hsζ : tsupport ζ ⊆ Ioo a b) (i : Fin n) (k : Fin (n + 1)) :
    ContDiff ℝ ∞ (fun y : Domain (n + 1) => annularTestField s β ζ ψ i y k) ∧
    HasCompactSupport (fun y : Domain (n + 1) => annularTestField s β ζ ψ i y k) ∧
    tsupport (fun y : Domain (n + 1) => annularTestField s β ζ ψ i y k) ⊆
      {y : Domain (n + 1) |
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∈ Ioo l r ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} := by
  have hβ0 : (0 : ℝ) ∉ tsupport β := fun h => (not_lt_of_ge hl) (hsβ h).1
  have hV := contDiff_annularTestField s hβ hζ hψ hβ0 i
  have hcompact := hasCompactSupport_annularTestField s hcβ hcζ ψ i
  have hcomponent : ContDiff ℝ ∞ (fun y : Domain (n + 1) => annularTestField s β ζ ψ i y k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hV
  have hsub : tsupport (fun y : Domain (n + 1) => annularTestField s β ζ ψ i y k) ⊆
      tsupport (annularTestField s β ζ ψ i) := by
    apply closure_mono
    intro y hy hz
    exact hy (congrArg (fun z : Domain (n + 1) => z k) hz)
  refine ⟨hcomponent, ?_, hsub.trans (tsupport_annularTestField_subset_collar s hsβ hsζ ψ i)⟩
  exact hcompact.of_isClosed_subset (isClosed_tsupport _) hsub

end StratificationTheory
