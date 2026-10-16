module

public import StratificationTheory.Foundation.RadialL2Transfer
public import HarmonicMaps.Analysis.AffineEnergyScaling
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Angular Hilbert--Schmidt energy of actual column families

Actual columnwise L2 data supply every finite integral in the tangential
projection identity. The energy is the sum of squared column L2 norms.
Native sphere measure and polar angular measure agree in positive dimension.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators

namespace StratificationTheory

/-- The actual radial contraction of an angular L2 column family belongs to L2. -/
theorem memLp_two_angular_radial_contraction {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    MemLp (fun θ : sphere (0 : Domain n) 1 => ∑ j : Fin n, θ.val j • A θ j)
      2 (volume : Measure (Domain n)).toSphere := by
  have hC (j : Fin n) : MemLp (fun θ : sphere (0 : Domain n) 1 => θ.val j) ∞
      (volume : Measure (Domain n)).toSphere := by
    have hc : Continuous (fun θ : sphere (0 : Domain n) 1 => θ.val j) :=
      (EuclideanSpace.proj j).continuous.comp continuous_subtype_val
    exact hc.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (volume : Measure (Domain n)).toSphere
  exact memLp_finsetSum Finset.univ (fun j _ => (hA j).smul (r := 2) (hC j))

/-- The actual radial contraction has a finite vector-valued Bochner integral. -/
theorem integrable_angular_radial_contraction {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    Integrable (fun θ : sphere (0 : Domain n) 1 => ∑ j : Fin n, θ.val j • A θ j)
      (volume : Measure (Domain n)).toSphere :=
  (memLp_two_angular_radial_contraction hA).integrable (by norm_num)

/-- The squared norm of the same actual radial contraction is integrable. -/
theorem integrable_angular_radial_contraction_sq {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    Integrable (fun θ : sphere (0 : Domain n) 1 => ‖∑ j : Fin n, θ.val j • A θ j‖ ^ 2)
      (volume : Measure (Domain n)).toSphere :=
  (memLp_two_angular_radial_contraction hA).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

/-- Actual angular column L2 membership supplies finite HS-density integrability. -/
theorem integrable_angular_hsNormSq {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (A θ))
      (volume : Measure (Domain n)).toSphere :=
  integrable_finsetSum Finset.univ
    (fun i _ => (hA i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))

/-- The HS density of the same actual tangentially projected columns is integrable. -/
theorem integrable_angular_hsNormSq_tangentialColumns {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (tangentialColumns θ (A θ)))
      (volume : Measure (Domain n)).toSphere :=
  integrable_angular_hsNormSq (fun i => memLp_two_tangential_column hA i)

/-- Tangential projection removes exactly the actual radial-contraction L2
energy from the actual angular HS energy. -/
theorem integral_angular_hsNormSq_tangentialColumns_eq {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    (∫ θ : sphere (0 : Domain n) 1, hsNormSq (tangentialColumns θ (A θ))
      ∂(volume : Measure (Domain n)).toSphere) =
        (∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ)
          ∂(volume : Measure (Domain n)).toSphere) -
        ∫ θ : sphere (0 : Domain n) 1, ‖∑ j : Fin n, θ.val j • A θ j‖ ^ 2
          ∂(volume : Measure (Domain n)).toSphere := by
  simp_rw [hsNormSq_tangentialColumns]
  exact integral_sub (integrable_angular_hsNormSq hA) (integrable_angular_radial_contraction_sq hA)

/-- Tangential projection decreases the actual integrated angular HS energy. -/
theorem integral_angular_hsNormSq_tangentialColumns_le {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere) :
    (∫ θ : sphere (0 : Domain n) 1, hsNormSq (tangentialColumns θ (A θ))
      ∂(volume : Measure (Domain n)).toSphere) ≤
        ∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ)
          ∂(volume : Measure (Domain n)).toSphere := by
  rw [integral_angular_hsNormSq_tangentialColumns_eq hA]
  exact sub_le_self _ (integral_nonneg fun θ => sq_nonneg _)

/-- Any real scalar multiple of the projected angular columns has finite HS energy. -/
theorem integrable_angular_hsNormSq_scaled_tangentialColumns {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere)
    (r : ℝ) :
    Integrable (fun θ : sphere (0 : Domain n) 1 =>
      hsNormSq (fun i => r • tangentialColumns θ (A θ) i))
        (volume : Measure (Domain n)).toSphere := by
  simp_rw [hsNormSq_const_smul]
  exact (integrable_angular_hsNormSq_tangentialColumns hA).const_mul (r ^ 2)

/-- The integrated HS energy of the same projected column family scales by
exactly the square of every real scalar. -/
theorem integral_angular_hsNormSq_scaled_tangentialColumns_eq {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q} (r : ℝ) :
    (∫ θ : sphere (0 : Domain n) 1,
      hsNormSq (fun i => r • tangentialColumns θ (A θ) i)
        ∂(volume : Measure (Domain n)).toSphere) =
          r ^ 2 * ∫ θ : sphere (0 : Domain n) 1, hsNormSq (tangentialColumns θ (A θ))
            ∂(volume : Measure (Domain n)).toSphere := by
  simp_rw [hsNormSq_const_smul]
  exact integral_const_mul _ _

/-- The scaled actual projected HS energy is bounded by the same scalar square
times the actual unprojected angular HS energy. -/
theorem integral_angular_hsNormSq_scaled_tangentialColumns_le {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere)
    (r : ℝ) :
    (∫ θ : sphere (0 : Domain n) 1,
      hsNormSq (fun i => r • tangentialColumns θ (A θ) i)
        ∂(volume : Measure (Domain n)).toSphere) ≤
          r ^ 2 * ∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ)
            ∂(volume : Measure (Domain n)).toSphere := by
  rw [integral_angular_hsNormSq_scaled_tangentialColumns_eq]
  exact mul_le_mul_of_nonneg_left (integral_angular_hsNormSq_tangentialColumns_le hA) (sq_nonneg r)

/-- The sum of the squared norms of the actual column L2 classes equals the
actual HS integral for the very same function family and membership proofs. -/
theorem sum_column_Lp_norm_sq_eq_integral_angular_hsNormSq {n q : ℕ}
    {μ : Measure (sphere (0 : Domain n) 1)}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 μ) :
    (∑ i : Fin n, ‖(hA i).toLp (fun θ => A θ i)‖ ^ 2) =
      ∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ) ∂μ := by
  simp_rw [Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hA _)]
  exact (integral_finsetSum Finset.univ
    (fun i _ => (hA i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))).symm

/-- The exact projection-energy identity uses the native Euclidean sphere
measure in every positive dimension. -/
theorem integral_native_hsNormSq_tangentialColumns_eq {n q : ℕ} (hn : 0 < n)
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))) :
    (∫ θ : sphere (0 : Domain n) 1, hsNormSq (tangentialColumns θ (A θ))
      ∂Measure.euclideanHausdorffMeasure (n - 1)) =
        (∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ)
          ∂Measure.euclideanHausdorffMeasure (n - 1)) -
        ∫ θ : sphere (0 : Domain n) 1, ‖∑ j : Fin n, θ.val j • A θ j‖ ^ 2
          ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at hA ⊢
  exact integral_angular_hsNormSq_tangentialColumns_eq hA

/-- The scaled projection bound uses the same actual columns and native
Euclidean sphere measure, for arbitrary real scalars. -/
theorem integral_native_hsNormSq_scaled_tangentialColumns_le {n q : ℕ} (hn : 0 < n)
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)))
    (r : ℝ) :
    (∫ θ : sphere (0 : Domain n) 1,
      hsNormSq (fun i => r • tangentialColumns θ (A θ) i)
        ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          r ^ 2 * ∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at hA ⊢
  exact integral_angular_hsNormSq_scaled_tangentialColumns_le hA r

end StratificationTheory
