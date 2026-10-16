module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differential and column algebra of spherical projection

Normalization is smooth on the punctured Euclidean domain. Its differential
is the reciprocal radius times the orthogonal projection onto the radial
orthogonal complement. Projection of the displayed ambient gradient columns
has an exact Hilbert--Schmidt square identity and vanishing radial component.
-/

public section

open HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators RealInnerProductSpace ContDiff

namespace StratificationTheory

/-- The literal differential formula of normalization, defined only at actual
nonzero points. -/
@[expose] noncomputable def normalizationDifferential {n : ℕ}
    (x : {x : Domain n // x ≠ 0}) : Domain n →L[ℝ] Domain n :=
  ‖x.val‖⁻¹ • ContinuousLinearMap.id ℝ (Domain n) -
    (‖x.val‖⁻¹ ^ 3) • (innerSL ℝ x.val).smulRight x.val

private theorem hasFDerivAt_norm_nonzero {n : ℕ} {x : Domain n} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Domain n => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hfun : (fun y : Domain n => Real.sqrt (‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  have hcoef : (1 / (2 * ‖x‖)) * 2 = ‖x‖⁻¹ := by
    field_simp
  rw [hfun, Real.sqrt_sq (norm_nonneg x)] at h
  have hmap : (1 / (2 * ‖x‖)) • (2 • (innerSL ℝ x)) = ‖x‖⁻¹ • innerSL ℝ x := by
    rw [two_smul, smul_add, ← add_smul]
    congr 1
    field_simp
    norm_num
  rw [hmap] at h
  exact h

/-- At every actual nonzero point, normalization has the displayed Fréchet
differential. -/
theorem hasFDerivAt_normalization {n : ℕ} (x : {x : Domain n // x ≠ 0}) :
    HasFDerivAt (fun y : Domain n => ‖y‖⁻¹ • y) (normalizationDifferential x) x.val := by
  have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
  have h := (hasDerivAt_inv hn).comp_hasFDerivAt x.val
    (hasFDerivAt_norm_nonzero x.property)
  have hcoef : -(‖x.val‖ ^ 2)⁻¹ * ‖x.val‖⁻¹ = -(‖x.val‖⁻¹ ^ 3) := by
    rw [inv_pow]
    ring
  rw [smul_smul, hcoef] at h
  have hp := h.smul (hasFDerivAt_id x.val)
  change HasFDerivAt (fun y : Domain n => ‖y‖⁻¹ • y)
    (‖x.val‖⁻¹ • ContinuousLinearMap.id ℝ (Domain n) +
      (-(‖x.val‖⁻¹ ^ 3) • innerSL ℝ x.val).smulRight x.val) x.val at hp
  have hmap : ‖x.val‖⁻¹ • ContinuousLinearMap.id ℝ (Domain n) +
      (-(‖x.val‖⁻¹ ^ 3) • innerSL ℝ x.val).smulRight x.val = normalizationDifferential x := by
    apply ContinuousLinearMap.ext
    intro v
    change ‖x.val‖⁻¹ • v + (-(‖x.val‖⁻¹ ^ 3) * inner ℝ x.val v) • x.val =
      ‖x.val‖⁻¹ • v - (‖x.val‖⁻¹ ^ 3) • (inner ℝ x.val v • x.val)
    simp only [mul_smul, neg_smul, sub_eq_add_neg]
  rw [hmap] at hp
  exact hp

/-- Normalization is smooth throughout the actual punctured Euclidean domain. -/
theorem contDiffOn_normalization {n : ℕ} :
    ContDiffOn ℝ ∞ (fun y : Domain n => ‖y‖⁻¹ • y) ({0}ᶜ : Set (Domain n)) := by
  have hn : ContDiffOn ℝ ∞ (fun y : Domain n => ‖y‖) ({0}ᶜ : Set (Domain n)) :=
    contDiffOn_id.norm ℝ (fun _ hy => hy)
  exact (hn.inv (fun y hy => norm_ne_zero_iff.mpr hy)).smul contDiffOn_id

/-- Literal projection of ambient gradient columns onto the source tangent
directions at a unit-sphere point. -/
@[expose] def tangentialColumns {n q : ℕ} (θ : sphere (0 : Domain n) 1)
    (A : Gradient n q) : Gradient n q :=
  fun i => A i - θ.val i • ∑ j : Fin n, θ.val j • A j

private theorem sphere_sum_sq_coordinates {n : ℕ} (θ : sphere (0 : Domain n) 1) :
    (∑ i : Fin n, (θ.val i) ^ 2) = 1 := by
  have hn : ‖θ.val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using θ.property
  rw [← EuclideanSpace.real_norm_sq_eq, hn]
  norm_num

/-- Tangential column projection removes exactly the squared norm of the
actual radial column from the HS square. -/
theorem hsNormSq_tangentialColumns {n q : ℕ} (θ : sphere (0 : Domain n) 1)
    (A : Gradient n q) :
    hsNormSq (tangentialColumns θ A) =
      hsNormSq A - ‖∑ j : Fin n, θ.val j • A j‖ ^ 2 := by
  let b : Ambient q := ∑ j : Fin n, θ.val j • A j
  have hcross : (∑ i : Fin n, θ.val i * inner ℝ (A i) b) = ‖b‖ ^ 2 := by
    calc
      _ = ∑ i : Fin n, inner ℝ (θ.val i • A i) b :=
        Finset.sum_congr rfl fun i _ => (real_inner_smul_left (A i) b (θ.val i)).symm
      _ = inner ℝ b b := (sum_inner Finset.univ (fun i => θ.val i • A i) b).symm
      _ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
  have hcol (i : Fin n) : ‖A i - θ.val i • b‖ ^ 2 =
      ‖A i‖ ^ 2 - 2 * (θ.val i * inner ℝ (A i) b) + (θ.val i) ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    try ring
  change (∑ i : Fin n, ‖A i - θ.val i • b‖ ^ 2) =
    (∑ i : Fin n, ‖A i‖ ^ 2) - ‖b‖ ^ 2
  simp_rw [hcol]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hcross, sphere_sum_sq_coordinates]
  ring

/-- Tangential projection never increases the actual HS density. -/
theorem hsNormSq_tangentialColumns_le {n q : ℕ} (θ : sphere (0 : Domain n) 1)
    (A : Gradient n q) : hsNormSq (tangentialColumns θ A) ≤ hsNormSq A := by
  rw [hsNormSq_tangentialColumns]
  exact sub_le_self _ (sq_nonneg _)

/-- The projected columns have zero actual radial contraction. -/
theorem sum_smul_tangentialColumns_eq_zero {n q : ℕ} (θ : sphere (0 : Domain n) 1)
    (A : Gradient n q) : (∑ i : Fin n, θ.val i • tangentialColumns θ A i) = 0 := by
  simp only [tangentialColumns, smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  simp_rw [← sq]
  rw [sphere_sum_sq_coordinates, one_smul, sub_self]

end StratificationTheory
