module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# L2 pullback and bounded column operations

Finite domination of the actual pushforward measure transfers original L2
data and convergence. Bounded scalar coefficients and finite column sums
preserve that convergence.
-/

public section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

theorem memLp_comp_of_map_le_smul
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y}
    {F : X → Y} (hF : AEMeasurable F μ) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map F μ ≤ c • ν) {p : ℝ≥0∞} {f : Y → E}
    (hf : MemLp f p ν) : MemLp (f ∘ F) p μ :=
  (hf.of_measure_le_smul hc hmap).comp_of_map hF

theorem eLpNorm_comp_le_of_map_le_smul
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y}
    {F : X → Y} (hF : AEMeasurable F μ) {c : ℝ≥0∞}
    (hmap : Measure.map F μ ≤ c • ν) {p : ℝ≥0∞} {f : Y → E}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm (f ∘ F) p μ ≤ c ^ (1 / p).toReal * eLpNorm f p ν := by
  have hfmap := hf.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)
  rw [← eLpNorm_map_measure hfmap hF]
  exact eLpNorm_le_of_measure_le_smul hmap

theorem tendsto_eLpNorm_comp_zero_of_map_le_smul
    {ι X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y}
    {F : X → Y} (hF : AEMeasurable F μ) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map F μ ≤ c • ν) {p : ℝ≥0∞}
    {l : Filter ι} {f : ι → Y → E}
    (hf : ∀ i, AEStronglyMeasurable (f i) ν)
    (hlim : Tendsto (fun i => eLpNorm (f i) p ν) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm ((f i) ∘ F) p μ) l (𝓝 0) := by
  have hfinite : c ^ (1 / p).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc
  have hbound := ENNReal.Tendsto.const_mul hlim (Or.inr hfinite)
  rw [mul_zero] at hbound
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) (fun i => eLpNorm_comp_le_of_map_le_smul hF hmap (hf i))

theorem tendsto_eLpNorm_two_bounded_smul_zero
    {ι X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {a : X → ℝ} (ha : MemLp a ∞ μ)
    {l : Filter ι} {f : ι → X → E}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hlim : Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => a x • f i x) 2 μ) l (𝓝 0) := by
  have hbound := ENNReal.Tendsto.const_mul hlim (Or.inr ha.eLpNorm_lt_top.ne)
  rw [mul_zero] at hbound
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le)
    (fun i => eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 (hf i) a)

theorem tendsto_eLpNorm_two_finite_sum_zero
    {ι X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {l : Filter ι} {n : ℕ} {f : Fin n → ι → X → E}
    (hf : ∀ j i, AEStronglyMeasurable (f j i) μ)
    (hlim : ∀ j, Tendsto (fun i => eLpNorm (f j i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => ∑ j, f j i x) 2 μ) l (𝓝 0) := by
  have hsum : Tendsto (fun i => ∑ j, eLpNorm (f j i) 2 μ) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro i
  change eLpNorm (fun x => ∑ j, f j i x) 2 μ ≤ ∑ j, eLpNorm (f j i) 2 μ
  have heq : (fun x => ∑ j, f j i x) = ∑ j, f j i := by
    funext x
    exact (Finset.sum_apply x Finset.univ (fun j => f j i)).symm
  rw [heq]
  exact eLpNorm_sum_le (s := Finset.univ) (fun j _ => hf j i)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

end StratificationTheory
