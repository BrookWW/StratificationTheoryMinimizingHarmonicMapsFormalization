module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

public section

open Filter
open scoped Topology ENNReal

namespace StratificationTheory.Compactness

private theorem norm_sq_support_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x u : H) : 2 * inner ℝ x u - ‖u‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := sq_nonneg ‖x - u‖
  rw [norm_sub_sq_real] at h
  linarith

/-- Convergence of the pairing with the limit gives lower semicontinuity of
squared norm in the extended nonnegative reals, without a uniform norm bound. -/
theorem norm_sq_le_liminf_of_inner_tendsto {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {l : Filter ι} [NeBot l] {f : ι → H} {u : H}
    (hinner : Tendsto (fun k => inner ℝ (f k) u) l (𝓝 (inner ℝ u u))) :
    ENNReal.ofReal (‖u‖ ^ 2) ≤ l.liminf (fun k => ENNReal.ofReal (‖f k‖ ^ 2)) := by
  have hReal : Tendsto (fun k => 2 * inner ℝ (f k) u - ‖u‖ ^ 2) l (𝓝 (‖u‖ ^ 2)) := by
    have h := (hinner.const_mul 2).sub_const (‖u‖ ^ 2)
    have heq : 2 * inner ℝ u u - ‖u‖ ^ 2 = ‖u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]; ring
    rwa [heq] at h
  have hENN := ENNReal.tendsto_ofReal hReal
  have hle := liminf_le_liminf (f := l) (Eventually.of_forall fun k =>
    ENNReal.ofReal_le_ofReal (norm_sq_support_bound (f k) u))
  rw [hENN.liminf_eq] at hle
  exact hle

/-- Weak pairing convergence supplies the eventual real lower norm bound at
every positive tolerance. -/
theorem eventually_norm_sq_lower_bound_of_inner_tendsto {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {l : Filter ι} {f : ι → H} {u : H}
    (hinner : Tendsto (fun k => inner ℝ (f k) u) l (𝓝 (inner ℝ u u)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in l, ‖u‖ ^ 2 ≤ ‖f k‖ ^ 2 + ε := by
  have hReal : Tendsto (fun k => 2 * inner ℝ (f k) u - ‖u‖ ^ 2) l (𝓝 (‖u‖ ^ 2)) := by
    have h := (hinner.const_mul 2).sub_const (‖u‖ ^ 2)
    have heq : 2 * inner ℝ u u - ‖u‖ ^ 2 = ‖u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]; ring
    rwa [heq] at h
  have hevent := hReal.eventually_const_lt (by linarith : ‖u‖ ^ 2 - ε < ‖u‖ ^ 2)
  filter_upwards [hevent] with k hk
  linarith [norm_sq_support_bound (f k) u]

end StratificationTheory.Compactness
