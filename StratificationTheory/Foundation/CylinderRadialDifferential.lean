module

public import StratificationTheory.Foundation.RadialSobolevPullback
import Mathlib.Analysis.Calculus.ContDiff.Basic

public section

open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff

namespace StratificationTheory

/-- Normalizing the spatial block while keeping the interval block fixed is
smooth on the actual ambient domain where the spatial block is nonzero. -/
theorem contDiffOn_cylinder_spatial_normalization {n : ℕ} :
    let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
    ContDiffOn ℝ ∞ (fun x : Domain (n + 1) =>
      e.symm (‖(e x).1‖⁻¹ • (e x).1, (e x).2))
        {x : Domain (n + 1) | (e x).1 ≠ 0} := by
  dsimp only
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
  have hfirst : ContDiffOn ℝ ∞ (fun x : Domain (n + 1) => (e x).1)
      {x : Domain (n + 1) | (e x).1 ≠ 0} :=
    (contDiff_fst.comp e.contDiff).contDiffOn
  have hn := contDiffOn_normalization.comp hfirst (fun _ hx => hx)
  have hsecond : ContDiffOn ℝ ∞ (fun x : Domain (n + 1) => (e x).2)
      {x : Domain (n + 1) | (e x).1 ≠ 0} :=
    (contDiff_snd.comp e.contDiff).contDiffOn
  exact e.symm.contDiff.comp_contDiffOn (hn.prodMk hsecond)

/-- The full ambient differential is the spatial normalization differential
and the unchanged interval coordinate, transported by the canonical split. -/
theorem hasFDerivAt_cylinder_spatial_normalization {n : ℕ}
    (x : Domain (n + 1))
    (hx : (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) x).1 ≠ 0) :
    let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
    HasFDerivAt (fun y : Domain (n + 1) =>
      e.symm (‖(e y).1‖⁻¹ • (e y).1, (e y).2))
      (e.symm.toContinuousLinearMap.comp
        (((normalizationDifferential ⟨(e x).1, hx⟩).comp
          ((ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)).prod
          ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap))) x := by
  dsimp only
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
  have hfirst := (ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).hasFDerivAt.comp
    x e.hasFDerivAt
  have hnorm := (hasFDerivAt_normalization ⟨(e x).1, hx⟩).comp x hfirst
  have hsecond := (ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).hasFDerivAt.comp
    x e.hasFDerivAt
  exact e.symm.hasFDerivAt.comp x (hnorm.prodMk hsecond)

/-- Spatial normalization leaves every actual interval-block direction
unchanged in its ambient Fréchet derivative. -/
theorem fderiv_cylinder_spatial_normalization_interval_direction {n : ℕ}
    (x : Domain (n + 1))
    (hx : (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) x).1 ≠ 0)
    (t : Domain 1) :
    let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
    fderiv ℝ (fun y : Domain (n + 1) =>
      e.symm (‖(e y).1‖⁻¹ • (e y).1, (e y).2)) x (e.symm (0, t)) = e.symm (0, t) := by
  dsimp only
  rw [(hasFDerivAt_cylinder_spatial_normalization x hx).fderiv]
  simp
  exact map_zero _

/-- Smooth maps pulled back by the actual spatial normalization have their
classical ambient columns as weak gradients on every spatially punctured domain. -/
theorem hasWeakGradient_cylinder_radial_smooth_pullback {n q : ℕ}
    (U : OpenDomain (n + 1))
    (hU : ∀ x ∈ U.val,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) x).1 ≠ 0)
    {f : Domain (n + 1) → Ambient q} (hf : ContDiff ℝ ∞ f) :
    let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
    let w := fun x : Domain (n + 1) => f (e.symm (‖(e x).1‖⁻¹ • (e x).1, (e x).2))
    HasWeakGradient U w (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) := by
  dsimp only
  apply hasWeakGradient_of_contDiffOn
  exact hf.comp_contDiffOn ((contDiffOn_cylinder_spatial_normalization (n := n)).mono hU)

private theorem cylinder_memLp_of_continuousOn_compact {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Domain n → E} {K : Set (Domain n)}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    MemLp f 2 (volume.restrict K) := by
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  apply MemLp.of_bound (hf.aestronglyMeasurable hK.isClosed.measurableSet) C
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hxK
  exact hC x hxK

/-- Actual compact cylinder collars supply finite L2 data for the smooth
spatial radial pullback and every displayed ambient weak-gradient column. -/
theorem memW12_cylinder_radial_smooth_pullback {n q : ℕ}
    (U : OpenDomain (n + 1)) {K : Set (Domain (n + 1))} (hK : IsCompact K)
    (hUK : U.val ⊆ K)
    (hK0 : ∀ x ∈ K,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) x).1 ≠ 0)
    {f : Domain (n + 1) → Ambient q} (hf : ContDiff ℝ ∞ f) :
    let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
    let w := fun x : Domain (n + 1) => f (e.symm (‖(e x).1‖⁻¹ • (e x).1, (e x).2))
    MemW12 U w (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) := by
  dsimp only
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
  have hO : IsOpen {x : Domain (n + 1) | (e x).1 ≠ 0} :=
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (Domain n))).preimage
      (continuous_fst.comp e.continuous)
  have hw := hf.comp_contDiffOn (contDiffOn_cylinder_spatial_normalization (n := n))
  have hDw := hw.continuousOn_fderiv_of_isOpen hO (by simp)
  refine ⟨hasWeakGradient_cylinder_radial_smooth_pullback U (fun x hx => hK0 x (hUK hx)) hf,
    (cylinder_memLp_of_continuousOn_compact hK (hw.continuousOn.mono hK0)).mono_measure
      (Measure.restrict_mono_set volume hUK), ?_⟩
  intro i
  exact (cylinder_memLp_of_continuousOn_compact hK
    ((hDw.clm_apply continuousOn_const).mono hK0)).mono_measure
      (Measure.restrict_mono_set volume hUK)

end StratificationTheory
