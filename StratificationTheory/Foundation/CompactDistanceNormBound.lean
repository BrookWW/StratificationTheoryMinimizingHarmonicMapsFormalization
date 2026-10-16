module

public import HarmonicMaps.Sobolev
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Measure.OpenPos

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped BigOperators

namespace StratificationTheory

/-- An original almost-everywhere value constraint on the actual open
unit cube supplies a genuine point of its target set. -/
theorem target_nonempty_of_ae_unit_cube {n q : ℕ} (u : Domain n → Ambient q)
    {N : Set (Ambient q)}
    (hu : ∀ᵐ x ∂volume.restrict (⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1), u x ∈ N) :
    N.Nonempty := by
  let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
  have hB : IsOpen B := isOpen_iInter_of_finite fun k : Fin n =>
    isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous
  have hZero : (0 : Domain n) ∈ B := by
    apply mem_iInter.mpr
    intro k
    change (0 : ℝ) ∈ Ioo (-1 : ℝ) 1
    norm_num
  have hPos : 0 < (volume : Measure (Domain n)) B := hB.measure_pos volume ⟨0, hZero⟩
  have hNe : (volume : Measure (Domain n)).restrict B ≠ 0 := by
    rw [ne_eq, Measure.restrict_eq_zero]
    exact hPos.ne'
  letI : (ae ((volume : Measure (Domain n)).restrict B)).NeBot := ae_neBot.mpr hNe
  obtain ⟨x, hx⟩ := hu.exists
  exact ⟨u x, hx⟩

/-- The actual squared-distance bounds of a finite family of maps to one
compact nonempty target produce a common norm bound. No boundedness of the
new maps is assumed. -/
theorem exists_uniform_norm_bound_of_compact_distance {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] {q : ℕ} (μ : Measure X) (v : ι → X → Ambient q)
    {N : Set (Ambient q)} (hN : IsCompact N) (hne : N.Nonempty) (C : ι → ℝ)
    (hDist : ∀ j, ∀ᵐ x ∂μ, (infDist (v j x) N) ^ 2 ≤ C j) :
    ∃ M : ℝ, ∀ j, ∀ᵐ x ∂μ, ‖v j x‖ ≤ M := by
  classical
  obtain ⟨B, hB⟩ := hN.isBounded.exists_norm_le
  let M := |B| + ∑ j : ι, Real.sqrt (max (C j) 0)
  refine ⟨M, ?_⟩
  intro j
  filter_upwards [hDist j] with x hx
  obtain ⟨z, hz, hMin⟩ := hN.exists_infDist_eq_dist hne (v j x)
  have hSqrt : infDist (v j x) N ≤ Real.sqrt (max (C j) 0) :=
    Real.le_sqrt_of_sq_le (hx.trans (le_max_left _ _))
  have hSum : Real.sqrt (max (C j) 0) ≤ ∑ k : ι, Real.sqrt (max (C k) 0) :=
    Finset.single_le_sum (f := fun k : ι => Real.sqrt (max (C k) 0))
      (fun k _ => Real.sqrt_nonneg (max (C k) 0)) (Finset.mem_univ j)
  calc
    ‖v j x‖ ≤ ‖v j x - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
    _ = infDist (v j x) N + ‖z‖ := by rw [hMin, dist_eq_norm]
    _ ≤ Real.sqrt (max (C j) 0) + |B| := add_le_add hSqrt ((hB z hz).trans (le_abs_self B))
    _ ≤ M := by dsimp only [M]; linarith

end StratificationTheory
