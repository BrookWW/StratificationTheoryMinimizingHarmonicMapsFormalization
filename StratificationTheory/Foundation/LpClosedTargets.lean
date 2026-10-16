module

public import StratificationTheory.Foundation.IntervalClosedConstraints
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import StratificationTheory.Compactness.ClosedTargetLimit
import Mathlib.Topology.Sequences

/-!
# Closed pointwise targets in L2

For an arbitrary measure, L2 classes whose values lie almost everywhere in a
closed target form a closed set. Continuous interval curves in this set retain
the angular a.e. constraint at both endpoints. The same statement applies to
the unique interval representative of actual Banach weak derivative data.
-/

public section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- Almost-everywhere membership in a closed target defines a closed subset
of the actual L2 space, for an arbitrary measure. -/
theorem isClosed_lp_two_ae_mem {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {S : Set E} (hS : IsClosed S) :
    IsClosed {z : Lp E 2 μ | ∀ᵐ x ∂μ, z x ∈ S} := by
  apply IsSeqClosed.isClosed
  intro z u hz hconv
  have hnorm : Tendsto (fun k => ‖z k - u‖ₑ) atTop (𝓝 0) := by
    simpa only [sub_self, enorm_zero] using
      (hconv.sub (tendsto_const_nhds (x := u))).enorm
  have hdiff : ∀ k, eLpNorm ((z k : α → E) - (u : α → E)) 2 μ = ‖z k - u‖ₑ := by
    intro k
    exact (eLpNorm_congr_ae (Lp.coeFn_sub (z k) u)).symm.trans
      (Lp.enorm_def (z k - u)).symm
  have hraw : Tendsto (fun k => eLpNorm ((z k : α → E) - (u : α → E)) 2 μ)
      atTop (𝓝 0) := by
    simp_rw [hdiff]
    exact hnorm
  exact Compactness.ae_mem_closed_of_L2_limit hS (fun k => Lp.memLp (z k))
    (Lp.memLp u) hz hraw

/-- An actual continuous L2-valued interval curve with an interior time-a.e.
angular closed-target constraint satisfies it at every closed-interval time. -/
theorem continuous_interval_lp_two_ae_mem_closed {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {S : Set E} (hS : IsClosed S)
    {a b : ℝ} (hab : a < b) (F : C(Icc a b, Lp E 2 μ))
    (hF : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∀ᵐ x ∂μ, F ⟨t, ht.1.le, ht.2.le⟩ x ∈ S) :
    ∀ t : Icc a b, ∀ᵐ x ∂μ, F t x ∈ S :=
  continuous_interval_mem_closed_of_ae hab F (isClosed_lp_two_ae_mem hS) hF

/-- The unique L2-valued weak interval representative preserves the original
time-a.e. angular target constraint through both endpoints, together with its
full absolute-continuity, integral-increment and energy properties. -/
theorem lp_two_interval_weakDerivative_exists_unique_closed_representative
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} {S : Set E} (hS : IsClosed S)
    {a b : ℝ} (hab : a < b) {f g : ℝ → Lp E 2 μ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t, deriv φ t • f t) = -(∫ t, φ t • g t))
    (hfS : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ᵐ x ∂μ, f t x ∈ S) :
    ∃! F : C(Icc a b, Lp E 2 μ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b, F ⟨t, ht.1.le, ht.2.le⟩ = f t) ∧
      (∃ G : ℝ → Lp E 2 μ, AbsolutelyContinuousOnInterval G a b ∧
        ∀ t : Icc a b, G t = F t) ∧
      (∀ s t : Icc a b, F t - F s = ∫ y in (s : ℝ)..(t : ℝ), g y) ∧
      (∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤
        |(t : ℝ) - (s : ℝ)| * ∫ y in Ioo a b, ‖g y‖ ^ 2) ∧
      (∀ t : Icc a b, ‖F t‖ ^ 2 ≤ (2 / (b - a)) * (∫ y in Ioo a b, ‖f y‖ ^ 2) +
        2 * (b - a) * (∫ y in Ioo a b, ‖g y‖ ^ 2)) ∧
      ∀ t : Icc a b, ∀ᵐ x ∂μ, F t x ∈ S :=
  banach_interval_weakDerivative_exists_unique_closed_representative
    hab hf hg hw (isClosed_lp_two_ae_mem hS) hfS

end StratificationTheory
