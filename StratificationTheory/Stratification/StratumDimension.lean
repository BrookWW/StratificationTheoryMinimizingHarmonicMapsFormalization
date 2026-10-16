module

public import StratificationTheory.Stratification.StratumBasic
public import StratificationTheory.Stratification.SpineConcentrationPhysical
public import StratificationTheory.Stratification.DensityConcentrationCover

public section
open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set Filter Module
open scoped Topology ENNReal
namespace StratificationTheory

/-- Every actual stratum has native Hausdorff nullity at all exponents
above its index and Hausdorff dimension at most that index. Concentration
is produced from the original minimizing map and all its actual tangents. -/
theorem singularStratum_hausdorff_bounds {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) (j : ℕ) (hj : j ≤ n) :
    (∀ s : ℝ, (j : ℝ) < s →
      μH[s] (Subtype.val '' singularStratum hn N Ω u Du hu hTarget hMinimizer j) = 0) ∧
      dimH (Subtype.val '' singularStratum hn N Ω u Du hu hTarget hMinimizer j) ≤ (j : ℝ≥0∞) := by
  let A := singularStratum hn N Ω u Du hu hTarget hMinimizer j
  let f : Ω.val → ℝ := density hn hMinimizer hu hTarget
  have hCon : ∀ δ : PositiveRadius, ∀ a ∈ A, ∃ ε : PositiveRadius,
      ∀ r : PositiveRadius, r.val ≤ ε.val →
        ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
          ∀ x ∈ A, x.val ∈ ball a.val r.val → f a - ε.val ≤ f x →
            infDist x.val ((fun v : Domain n => a.val + v) '' (V : Set (Domain n))) <
              δ.val * r.val := by
    intro δ a ha
    have hMember := (mem_singularStratum_iff hn N Ω u Du hu hTarget hMinimizer j a).mp ha
    obtain ⟨ε₀, hε₀, hNear⟩ := exists_affine_spine_concentration_at_stratum_point hn N Ω u Du
      hu hTarget hMinimizer a hMember.1 j hj hMember.2 δ.val δ.property
    obtain ⟨R, hR, hBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds a.property)
    let ε : PositiveRadius := ⟨min ε₀ R, lt_min hε₀ hR⟩
    refine ⟨ε, ?_⟩
    intro r hr
    have hrε₀ : r.val ≤ ε₀ := hr.trans (min_le_left _ _)
    have hrR : r.val ≤ R := hr.trans (min_le_right _ _)
    obtain ⟨V, hV, hDist⟩ := hNear r hrε₀ ((closedBall_subset_closedBall hrR).trans hBall)
    refine ⟨V, hV, ?_⟩
    intro x _hx hxBall hxDensity
    exact hDist x hxBall (by
      change f a - ε₀ ≤ f x
      have hε : ε.val ≤ ε₀ := min_le_left _ _
      linarith)
  exact ⟨hausdorffMeasure_image_zero_of_local_density_flatness Ω A f j hj hCon,
    dimH_image_le_of_local_density_flatness Ω A f j hj hCon⟩

end StratificationTheory
