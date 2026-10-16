module

public import StratificationTheory.Foundation.ConeSpatialTimeMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual spatial cone coordinates and uniform differential bounds

Spatial inverse radial coordinates leave the interpolation time unchanged.
They are smooth wherever the positive spatial height is nonzero. Bounded
Euclidean regions separated from zero spatial height give derivative bounds
before any source map or time interval is chosen.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ContDiff ENNReal
namespace StratificationTheory

/-- The actual inverse spatial cone chart is smooth on its positive-height
open set, and does not divide the independent time coordinate by the height. -/
theorem contDiffOn_spatial_cone_time_coordinates (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • (e ((E y).1)).1, (E y).2)
    ContDiffOn ℝ ∞ F {y | 0 < T y} := by
  intro e E T F
  have hspace : ContDiff ℝ ∞ (fun y : Domain (n + 1 + 1) => e ((E y).1)) :=
    e.contDiff.comp (contDiff_fst.comp E.contDiff)
  have hT : ContDiff ℝ ∞ T :=
    (EuclideanSpace.proj (0 : Fin 1) : Domain 1 →L[ℝ] ℝ).contDiff.comp
      (contDiff_snd.comp hspace)
  have hX : ContDiff ℝ ∞ (fun y : Domain (n + 1 + 1) => (e ((E y).1)).1) :=
    contDiff_fst.comp hspace
  have hI : ContDiffOn ℝ ∞ (fun y => (T y)⁻¹) {y | 0 < T y} :=
    hT.contDiffOn.inv (fun _ hy => ne_of_gt hy)
  exact e.symm.contDiff.comp_contDiffOn
    ((hI.smul hX.contDiffOn).prodMk (contDiff_snd.comp E.contDiff).contDiffOn)

/-- The actual chart has a uniform differential bound on every bounded
Euclidean region with spatial height separated from zero. Its constant precedes all source
Sobolev maps and interpolation time intervals. -/
theorem exists_spatial_cone_time_differential_bound (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (R : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • (e ((E y).1)).1, (E y).2)
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y, ‖y‖ ≤ R → ρ ≤ T y → ‖fderiv ℝ F y‖ ≤ L := by
  intro e E T F
  have hT : Continuous T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp (e.continuous.comp (continuous_fst.comp E.continuous)))
  let H : Set (Domain (n + 1 + 1)) := {y | 0 < T y}
  let K : Set (Domain (n + 1 + 1)) := closedBall 0 R ∩ {y | ρ ≤ T y}
  have hH : IsOpen H := isOpen_lt continuous_const hT
  have hK : IsCompact K := (isCompact_closedBall (0 : Domain (n + 1 + 1)) R).inter_right
    (isClosed_le continuous_const hT)
  have hKH : K ⊆ H := fun _ hy => hρ.trans_le hy.2
  have hF : ContDiffOn ℝ ∞ F H := contDiffOn_spatial_cone_time_coordinates n
  have hDF : ContinuousOn (fderiv ℝ F) H := hF.continuousOn_fderiv_of_isOpen hH (by simp)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hDF.mono hKH)
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro y hy hTy
  exact (hM y ⟨mem_closedBall_zero_iff.mpr hy, hTy⟩).trans (le_max_left _ _)

end StratificationTheory
