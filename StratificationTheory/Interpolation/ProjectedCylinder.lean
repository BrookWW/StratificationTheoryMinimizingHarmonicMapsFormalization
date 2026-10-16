module

public import StratificationTheory.Interpolation.ProjectedCollar
public import StratificationTheory.Foundation.CylinderTracePostcomposition
public import StratificationTheory.Foundation.CylinderTraceAlgebra

/-!
# Uniform target projection of full cylinder maps

One smooth ambient operator works for every full cylinder Sobolev map whose
native class lies in its tube. It produces target values on the cylinder and
at every trace time, and preserves each already target-valued trace class.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff

namespace StratificationTheory.Interpolation

/-- A target-dependent tube and one operator preserve full cylinder Sobolev
membership and every target-valued named trace. The tube condition concerns
the original native cylinder class and is the actual input for projection. -/
theorem exists_projected_cylinder_operator {q : ℕ} (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q),
      0 < ρ ∧ ContDiff ℝ ∞ Q ∧
      (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (hab : a < b)
        (v : unitCylinder n a b → Ambient q) (hv : MemCylinderW12 hn hab v),
        (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
          infDist (v y) N.carrierSet < ρ) →
        ∃ hQv : MemCylinderW12 hn hab (Q ∘ v),
          (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
            (Q ∘ v) y ∈ N.carrierSet ∧ ‖fderiv ℝ Q (v y)‖ ≤ 2) ∧
          (∀ t : Icc a b, ∀ᵐ θ : sphere (0 : Domain n) 1
            ∂Measure.euclideanHausdorffMeasure (n - 1),
              cylinderTrace hn hab (Q ∘ v) hQv t θ ∈ N.carrierSet) ∧
          ∀ t : Icc a b,
            (∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
              cylinderTrace hn hab v hv t θ ∈ N.carrierSet) →
            cylinderTrace hn hab (Q ∘ v) hQv t = cylinderTrace hn hab v hv t := by
  obtain ⟨ρ, Q, hρ, _hbase, hQ, ⟨L, _hL, hQL⟩, hfix, hnear⟩ :=
    exists_smooth_target_projection N
  refine ⟨ρ, Q, hρ, hQ, hfix, ?_⟩
  intro n hn a b hab v hv htube
  have hQv := memCylinderW12_postcompose hn hab v hv Q hQ L hQL
  have hvalues : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      (Q ∘ v) y ∈ N.carrierSet ∧ ‖fderiv ℝ Q (v y)‖ ≤ 2 := by
    filter_upwards [htube] with y hy
    obtain ⟨_ht, _heq, hmem, hD⟩ := hnear (v y) hy
    exact ⟨hmem, hD⟩
  refine ⟨hQv, hvalues,
    cylinderTrace_mem_closed hn hab (Q ∘ v) hQv N.isClosed (hvalues.mono fun _ h => h.1), ?_⟩
  intro t htN
  obtain ⟨hT, hTeq⟩ := cylinderTrace_postcompose hn hab v hv Q hQ L hQL t
  rw [hTeq]
  apply Lp.ext
  filter_upwards [hT.coeFn_toLp, htN] with θ hθ hNθ
  exact hθ.trans (hfix _ hNθ)

end StratificationTheory.Interpolation
