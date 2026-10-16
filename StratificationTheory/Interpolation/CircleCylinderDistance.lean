module

public import StratificationTheory.Interpolation.CircleInterpolationBound
public import StratificationTheory.Frozen.CylinderSobolev
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import StratificationTheory.Foundation.CylinderParamMeasure
import StratificationTheory.Foundation.CylinderPointCoordinates
import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
import StratificationTheory.Foundation.CylinderSurfaceMeasure

/-!
# Native distance bound for the affine circle cylinder connector

One native-a.e. target-valued endpoint controls the distance of the literal
ambient affine connector. The native circle difference bound transfers
through the actual compact sphere-interval parametrization of the cylinder.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory

private theorem infDist_affine_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : Set E) {x y : E} (hN : x ∈ N ∨ y ∈ N) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (infDist ((1 - α) • x + α • y) N) ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hnorm : infDist ((1 - α) • x + α • y) N ≤ ‖x - y‖ := by
    rcases hN with hx | hy
    · calc
        _ ≤ dist ((1 - α) • x + α • y) x := infDist_le_dist_of_mem hx
        _ = ‖α • (y - x)‖ := by
          rw [dist_eq_norm]
          congr 1
          simp only [sub_smul, one_smul, smul_sub]
          abel
        _ = α * ‖y - x‖ := by rw [norm_smul, Real.norm_of_nonneg hα]
        _ ≤ ‖y - x‖ := mul_le_of_le_one_left (norm_nonneg _) hα1
        _ = ‖x - y‖ := norm_sub_rev _ _
    · calc
        _ ≤ dist ((1 - α) • x + α • y) y := infDist_le_dist_of_mem hy
        _ = ‖(1 - α) • (x - y)‖ := by
          rw [dist_eq_norm]
          congr 1
          simp only [sub_smul, one_smul, smul_sub]
          abel
        _ = (1 - α) * ‖x - y‖ := by rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hα1)]
        _ ≤ ‖x - y‖ := mul_le_of_le_one_left (norm_nonneg _) (sub_le_self 1 hα)
  exact pow_le_pow_left₀ infDist_nonneg hnorm 2

/-- If either original endpoint is native-a.e. valued in an arbitrary target
set, the literal ambient affine connector satisfies the native physical
cylinder distance bound. No raw continuity or pointwise endpoint membership
is required. -/
theorem circle_affine_cylinder_distance_bound {q : ℕ} {a b : ℝ} (hab : a < b)
    (u v : sphere (0 : Domain 2) 1 → Ambient q)
    (hu : MemSphereW12 (Nat.le_refl 2) u) (hv : MemSphereW12 (Nat.le_refl 2) v)
    (N : Set (Ambient q))
    (hN : (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)), u θ ∈ N) ∨
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)), v θ ∈ N)) :
    let σ : Measure (sphere (0 : Domain 2) 1) := Measure.euclideanHausdorffMeasure 1
    let A := ∫ θ : sphere (0 : Domain 2) 1,
      ∑ i : Fin 2, (‖(sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2 +
        ‖(sphereGradient (Nat.le_refl 2) v hv i) θ‖ ^ 2) ∂σ
    let D := ∫ θ : sphere (0 : Domain 2) 1, ‖u θ - v θ‖ ^ 2 ∂σ
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    ∀ᵐ c : unitCylinder 2 a b ∂Measure.euclideanHausdorffMeasure 2,
      (infDist ((1 - ((e c.val).2 0 - a) / (b - a)) • u ⟨(e c.val).1, c.property.1⟩ +
        (((e c.val).2 0 - a) / (b - a)) • v ⟨(e c.val).1, c.property.1⟩) N) ^ 2 ≤
          8 * Real.sqrt (A * D) + 8 * D := by
  intro σ A D e
  let p : sphere (0 : Domain 2) 1 × Icc a b → unitCylinder 2 a b := fun z =>
    ⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val), unitCylinder_param_mem z.1 z.2⟩
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  obtain ⟨hpEmb, hpMP⟩ := unitCylinder_param_measurePreserving (by decide : 0 < 2) a b
  have hmem : ∀ᵐ θ ∂σ, u θ ∈ N ∨ v θ ∈ N := by
    rcases hN with hNu | hNv
    · exact hNu.mono (fun _ h => Or.inl h)
    · exact hNv.mono (fun _ h => Or.inr h)
  have hdiff := circle_sobolev_difference_interpolation_bound u v hu hv
  have hpair : ∀ᵐ z : sphere (0 : Domain 2) 1 × Icc a b ∂σ.prod ν,
      u z.1 ∈ N ∨ v z.1 ∈ N := Measure.quasiMeasurePreserving_fst.ae hmem
  have hbound : ∀ᵐ z : sphere (0 : Domain 2) 1 × Icc a b ∂σ.prod ν,
      ‖u z.1 - v z.1‖ ^ 2 ≤ 8 * Real.sqrt (A * D) + 8 * D :=
    Measure.quasiMeasurePreserving_fst.ae hdiff
  rw [← hpMP.map_eq]
  apply hpEmb.ae_map_iff.mpr
  filter_upwards [hpair, hbound] with z hz hb
  have hlo : 0 ≤ (z.2.val - a) / (b - a) :=
    div_nonneg (sub_nonneg.mpr z.2.property.1) (sub_pos.mpr hab).le
  have hhi : (z.2.val - a) / (b - a) ≤ 1 :=
    (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right z.2.property.2 a)
  have hdist := (infDist_affine_sq_le N hz hlo hhi).trans hb
  dsimp only [e]
  simpa only [ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true] using hdist

end StratificationTheory
