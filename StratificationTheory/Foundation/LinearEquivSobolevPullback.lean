module

public import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Native Sobolev pullback by an actual linear coordinate isomorphism

The original weak graph is transported by a genuine continuous linear
equivalence. Its determinant supplies the exact native volume multiplier;
the transformed columns are the actual linear chain-rule columns.
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal
namespace StratificationTheory

theorem map_continuousLinearEquiv_volume {n : ℕ}
    (e : Domain n ≃L[ℝ] Domain n) :
    Measure.map e volume =
      ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹| • volume := by
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Domain n))
    (IsUnit.ne_zero e.toLinearEquiv.isUnit_det')

/-- The actual linear chart produces its own full weak pullback and chain
columns on the genuine inverse image of the original open domain. -/
theorem memW12_continuousLinearEquiv_preimage {n q : ℕ}
    (e : Domain n ≃L[ℝ] Domain n)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) :
    MemW12 ⟨e ⁻¹' Ω.val, Ω.property.preimage e.continuous⟩ (u ∘ e)
      (fun x i => ∑ j : Fin n, (e (EuclideanSpace.single i 1)) j • Du (e x) j) := by
  let U : OpenDomain n := ⟨e ⁻¹' Ω.val, Ω.property.preimage e.continuous⟩
  let c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹|
  have hmap : Measure.map e (volume.restrict U.val) = c • volume.restrict Ω.val := by
    change Measure.map e (volume.restrict (e ⁻¹' Ω.val)) = c • volume.restrict Ω.val
    rw [← Measure.restrict_map e.continuous.measurable Ω.property.measurableSet,
      map_continuousLinearEquiv_volume,Measure.restrict_smul]
  have hder (x : Domain n) : fderiv ℝ e x = e.toContinuousLinearMap := e.hasFDerivAt.fderiv
  have hp := memW12_smooth_open_domain_pullback hu U e e.contDiff.contDiffOn
    (fun _ h => h) ‖e.toContinuousLinearMap‖ (fun x _ => by rw [hder]) c
    ENNReal.ofReal_ne_top hmap.le
  have hcols : (fun x i => ∑ j : Fin n,
      (fderiv ℝ e x (EuclideanSpace.single i 1)) j • Du (e x) j) =
      (fun x i => ∑ j : Fin n, (e (EuclideanSpace.single i 1)) j • Du (e x) j) := by
    funext x i
    rw [hder]
    rfl
  rw [hcols] at hp
  exact hp

end StratificationTheory
