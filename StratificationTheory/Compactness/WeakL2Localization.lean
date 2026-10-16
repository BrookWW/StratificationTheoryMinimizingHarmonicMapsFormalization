module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

public section

open MeasureTheory Filter Set
open scoped Topology

namespace StratificationTheory.Compactness

private theorem inner_toLp_eq_raw_integral {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {g : α → E} (hg : MemLp g 2 μ) (v : Lp E 2 μ) :
    inner ℝ (hg.toLp g) v = ∫ x, inner ℝ (g x) (v x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

/-- Actual weak L2 integral limits are unique up to almost-everywhere equality. -/
theorem ae_eq_of_weak_L2_limits {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {f : ℕ → α → E} {g h : α → E}
    (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hfg : ∀ v : Lp E 2 μ, Tendsto (fun k => ∫ x, inner ℝ (f k x) (v x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (g x) (v x) ∂μ)))
    (hfh : ∀ v : Lp E 2 μ, Tendsto (fun k => ∫ x, inner ℝ (f k x) (v x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (h x) (v x) ∂μ))) :
    g =ᵐ[μ] h := by
  apply (hg.toLp_eq_toLp_iff hh).mp
  apply ext_inner_right ℝ
  intro v
  rw [inner_toLp_eq_raw_integral hg v, inner_toLp_eq_raw_integral hh v]
  exact tendsto_nhds_unique (hfg v) (hfh v)

/-- Weak L2 integral convergence restricts to every contained measurable region.
Every smaller-region test is extended by zero inside the larger-region proof. -/
theorem weak_L2_integral_convergence_mono {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {K T : Set α} (hK : MeasurableSet K) (hKT : K ⊆ T)
    {f : ℕ → α → E} {g : α → E}
    (hconv : ∀ w : Lp E 2 (μ.restrict T),
      Tendsto (fun k => ∫ x in T, inner ℝ (f k x) (w x) ∂μ)
        atTop (𝓝 (∫ x in T, inner ℝ (g x) (w x) ∂μ))) :
    ∀ v : Lp E 2 (μ.restrict K),
      Tendsto (fun k => ∫ x in K, inner ℝ (f k x) (v x) ∂μ)
        atTop (𝓝 (∫ x in K, inner ℝ (g x) (v x) ∂μ)) := by
  classical
  intro v
  have hvGlobal : MemLp (K.indicator (v : α → E)) 2 μ :=
    (memLp_indicator_iff_restrict hK).mpr (Lp.memLp v)
  have hvT := hvGlobal.mono_measure (Measure.restrict_le_self (s := T))
  let w := hvT.toLp (K.indicator (v : α → E))
  have heq (u : α → E) : (∫ x in T, inner ℝ (u x) (w x) ∂μ) =
      ∫ x in K, inner ℝ (u x) (v x) ∂μ := by
    have hAE : (fun x => inner ℝ (u x) (w x)) =ᵐ[μ.restrict T]
        K.indicator (fun x => inner ℝ (u x) (v x)) := by
      filter_upwards [hvT.coeFn_toLp] with x hx
      dsimp only [w] at hx ⊢
      rw [hx]
      by_cases hxK : x ∈ K
      · simp only [indicator_of_mem hxK]
      · simp only [indicator_of_notMem hxK, inner_zero_right]
    rw [integral_congr_ae hAE, setIntegral_indicator hK]
    rw [inter_eq_right.mpr hKT]
  simpa only [heq] using hconv w

end StratificationTheory.Compactness
