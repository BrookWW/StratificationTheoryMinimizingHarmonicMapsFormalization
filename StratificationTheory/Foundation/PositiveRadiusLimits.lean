module

public import StratificationTheory.Foundation.MonotoneLimitAtZero
import Mathlib.Topology.Algebra.Ring.Real

public section

open Filter Set
open scoped Topology

namespace StratificationTheory

/-- Positive radii ordered towards their infimum converge to zero in ℝ. -/
theorem positiveRadius_val_tendsto_zero :
    Tendsto (Subtype.val : Ioi (0 : ℝ) → ℝ) atBot (𝓝 (0 : ℝ)) := by
  have hwithin : Tendsto (Subtype.val : Ioi (0 : ℝ) → ℝ) atBot (𝓝[>] (0 : ℝ)) := by
    exact (tendsto_Ioi_atBot (f := id)).mp tendsto_id
  exact hwithin.mono_right nhdsWithin_le_nhds

/-- Multiplication by a fixed positive number preserves the radius filter at
zero. The proof uses cofinality, without extending the positive-radius carrier. -/
theorem positiveRadius_mul_tendsto_atBot {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun r : Ioi (0 : ℝ) =>
      (⟨ρ * r.val, mul_pos hρ r.property⟩ : Ioi (0 : ℝ))) atBot atBot := by
  apply tendsto_atBot_atBot_of_monotone
  · intro r s hrs
    change ρ * r.val ≤ ρ * s.val
    exact mul_le_mul_of_nonneg_left (show r.val ≤ s.val from hrs) hρ.le
  · intro s
    refine ⟨⟨s.val / ρ, div_pos s.property hρ⟩, ?_⟩
    change ρ * (s.val / ρ) ≤ s.val
    rw [mul_div_cancel₀ _ hρ.ne']

/-- Finite limits agree when two functions on positive radii are related by
one fixed positive dilation. -/
theorem positiveRadius_limit_eq_of_rescaling {f g : Ioi (0 : ℝ) → ℝ}
    {ρ L M : ℝ} (hρ : 0 < ρ) (hf : Tendsto f atBot (𝓝 L))
    (hg : Tendsto g atBot (𝓝 M))
    (hfg : ∀ r : Ioi (0 : ℝ), g r = f ⟨ρ * r.val, mul_pos hρ r.property⟩) :
    L = M := by
  have hcomp := hf.comp (positiveRadius_mul_tendsto_atBot hρ)
  have hlimit : Tendsto g atBot (𝓝 L) := by
    convert hcomp using 1
    funext r
    exact hfg r
  exact tendsto_nhds_unique hlimit hg

end StratificationTheory
