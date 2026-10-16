module

public import StratificationTheory.Frozen.FlatCover
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Ring

public section
open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set Filter Module
open scoped Topology ENNReal
namespace StratificationTheory

/-- Local density concentration gives Hausdorff nullity through countably
many uniform-radius density bins for each fixed approximation parameter. -/
theorem hausdorffMeasure_image_zero_of_local_density_flatness {n : ℕ}
    (Ω : OpenDomain n) (A : Set Ω.val) (f : Ω.val → ℝ)
    (j : ℕ) (hj : j ≤ n)
    (hCon : ∀ δ : PositiveRadius, ∀ a ∈ A, ∃ ε : PositiveRadius,
      ∀ r : PositiveRadius, r.val ≤ ε.val →
        ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
          ∀ x ∈ A, x.val ∈ ball a.val r.val → f a - ε.val ≤ f x →
            infDist x.val ((fun v : Domain n => a.val + v) '' (V : Set (Domain n))) <
              δ.val * r.val)
    (s : ℝ) (hjs : (j : ℝ) < s) :
    μH[s] (Subtype.val '' A) = 0 := by
  classical
  obtain ⟨β, _hβpos, hβlim, hFlat⟩ := flatApproximation_hausdorffMeasure_zero j hj
  obtain ⟨δ, hδ⟩ := (hβlim.eventually_lt_const (sub_pos.mpr hjs)).exists
  let e : ℕ → PositiveRadius := fun i => ⟨1 / ((i : ℝ) + 1), by positivity⟩
  let Good : ℕ → Ω.val → Prop := fun i a =>
    ∀ r : PositiveRadius, r.val ≤ (e i).val →
      ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
        ∀ x ∈ A, x.val ∈ ball a.val r.val → f a - (e i).val ≤ f x →
          infDist x.val ((fun v : Domain n => a.val + v) '' (V : Set (Domain n))) <
            δ.val * r.val
  let B : ℕ → ℤ → Set (Domain n) := fun i q => Subtype.val ''
    {a : Ω.val | a ∈ A ∧ Good i a ∧
      ((q : ℝ) - 1) * (e i).val < f a ∧ f a ≤ (q : ℝ) * (e i).val}
  have hBnull (i : ℕ) (q : ℤ) : μH[(j : ℝ) + β δ] (B i q) = 0 := by
    apply hFlat δ (B i q)
    refine ⟨e i, ?_⟩
    intro a ha r hr
    rcases ha with ⟨a, ⟨haA, haGood, _haLower, haUpper⟩, rfl⟩
    obtain ⟨V, hV, hNear⟩ := haGood r hr
    refine ⟨V, hV, ?_⟩
    rintro x ⟨⟨x, ⟨hxA, _hxGood, hxLower, _hxUpper⟩, rfl⟩, hxBall⟩
    apply hNear x hxA hxBall
    nlinarith only [haUpper, hxLower]
  have hCover : Subtype.val '' A ⊆ ⋃ i : ℕ, ⋃ q : ℤ, B i q := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨ε, hε⟩ := hCon δ a ha
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt ε.property
    have hei : (e i).val ≤ ε.val := hi.le
    have hGood : Good i a := by
      intro r hr
      obtain ⟨V, hV, hNear⟩ := hε r (hr.trans hei)
      refine ⟨V, hV, ?_⟩
      intro x hx hxBall hxDensity
      exact hNear x hx hxBall (by linarith)
    let q : ℤ := Int.ceil (f a / (e i).val)
    have hUpper : f a ≤ (q : ℝ) * (e i).val := by
      exact (div_le_iff₀ (e i).property).mp (Int.le_ceil _)
    have hLower : ((q : ℝ) - 1) * (e i).val < f a := by
      have h := Int.ceil_lt_add_one (f a / (e i).val)
      have hq : (q : ℝ) - 1 < f a / (e i).val := by dsimp only [q]; linarith
      exact (lt_div_iff₀ (e i).property).mp hq
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨q, ⟨a, ⟨ha, hGood, hLower, hUpper⟩, rfl⟩⟩⟩
  have hNull : μH[(j : ℝ) + β δ] (Subtype.val '' A) = 0 :=
    measure_mono_null hCover (measure_iUnion_null fun i => measure_iUnion_null (hBnull i))
  apply le_antisymm _ zero_le
  calc
    μH[s] (Subtype.val '' A) ≤ μH[(j : ℝ) + β δ] (Subtype.val '' A) :=
      hausdorffMeasure_mono (by linarith) _
    _ = 0 := hNull

/-- The same local concentration property bounds the actual Hausdorff
dimension of the ambient image by the plane dimension. -/
theorem dimH_image_le_of_local_density_flatness {n : ℕ}
    (Ω : OpenDomain n) (A : Set Ω.val) (f : Ω.val → ℝ)
    (j : ℕ) (hj : j ≤ n)
    (hCon : ∀ δ : PositiveRadius, ∀ a ∈ A, ∃ ε : PositiveRadius,
      ∀ r : PositiveRadius, r.val ≤ ε.val →
        ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
          ∀ x ∈ A, x.val ∈ ball a.val r.val → f a - ε.val ≤ f x →
            infDist x.val ((fun v : Domain n => a.val + v) '' (V : Set (Domain n))) <
              δ.val * r.val) :
    dimH (Subtype.val '' A) ≤ (j : ℝ≥0∞) := by
  apply dimH_le
  intro d hd
  by_contra hNot
  have hjd : (j : ℝ≥0∞) < d := lt_of_not_ge hNot
  have hjdReal : (j : ℝ) < (d : ℝ) := by exact_mod_cast hjd
  have hZero := hausdorffMeasure_image_zero_of_local_density_flatness Ω A f j hj hCon
    (d : ℝ) hjdReal
  exact (ENNReal.zero_ne_top : (0 : ℝ≥0∞) ≠ ⊤) (hZero.symm.trans hd)

end StratificationTheory
