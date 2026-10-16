module

public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.Monotone

public section

open Filter Set
open scoped Topology

namespace StratificationTheory

/-- On positive real numbers, `atBot` is the one-sided filter at zero. -/
theorem positiveRadius_atBot_eq :
    (atBot : Filter (Ioi (0 : ℝ))) =
      comap Subtype.val (𝓝[>] (0 : ℝ)) := by
  exact (comap_coe_Ioi_nhdsGT (0 : ℝ)).symm

/-- A function that is monotone on a bounded positive interval converges to
its infimum when the interval image has a real lower bound. -/
theorem tendsto_positive_atBot_csInf {f : Ioi (0 : ℝ) → ℝ} {R : ℝ}
    (hR : 0 < R) (hmono : MonotoneOn f {r | r.val < R})
    (hbound : BddBelow (f '' {r | r.val < R})) :
    Tendsto f atBot (𝓝 (sInf (f '' {r | r.val < R}))) := by
  have hnonempty : ({r : Ioi (0 : ℝ) | r.val < R} : Set (Ioi (0 : ℝ))).Nonempty :=
    ⟨⟨R / 2, half_pos hR⟩, half_lt_self hR⟩
  refine tendsto_order.mpr ⟨fun l hl => ?_, fun m hm => ?_⟩
  · filter_upwards [eventually_le_atBot (⟨R / 2, half_pos hR⟩ : Ioi (0 : ℝ))] with r hr
    have hrR : r.val < R := lt_of_le_of_lt hr (half_lt_self hR)
    exact hl.trans_le (csInf_le hbound (mem_image_of_mem f hrR))
  · obtain ⟨z, hzR, hzm⟩ : ∃ z : Ioi (0 : ℝ), z.val < R ∧ f z < m := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and, mem_setOf_eq] using
        exists_lt_of_csInf_lt (hnonempty.image f) hm
    filter_upwards [eventually_le_atBot z] with r hr
    exact (hmono (show r.val < R from lt_of_le_of_lt hr hzR) hzR hr).trans_lt hzm

/-- The finite limit of a locally monotone, lower-bounded function on positive
radii is unique. -/
theorem existsUnique_positive_atBot_limit {f : Ioi (0 : ℝ) → ℝ} {R : ℝ}
    (hR : 0 < R) (hmono : MonotoneOn f {r | r.val < R})
    (hbound : BddBelow (f '' {r | r.val < R})) :
    ∃! l : ℝ, Tendsto f atBot (𝓝 l) := by
  refine ⟨sInf (f '' {r | r.val < R}), tendsto_positive_atBot_csInf hR hmono hbound, ?_⟩
  intro l hl
  exact tendsto_nhds_unique hl (tendsto_positive_atBot_csInf hR hmono hbound)

/-- Every lower bound for the interval image is also a lower bound for its
limiting infimum. -/
theorem le_positive_csInf {f : Ioi (0 : ℝ) → ℝ} {R c : ℝ}
    (hR : 0 < R) (hbound : ∀ r : Ioi (0 : ℝ), r.val < R → c ≤ f r) :
    c ≤ sInf (f '' {r | r.val < R}) := by
  apply le_csInf
  · exact ⟨f ⟨R / 2, half_pos hR⟩, mem_image_of_mem f (half_lt_self hR)⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hbound r hr

/-- The infimum on any two positive intervals is the same when both interval
restrictions are monotone and have real lower bounds. -/
theorem positive_csInf_eq {f : Ioi (0 : ℝ) → ℝ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S)
    (hmonoR : MonotoneOn f {r | r.val < R})
    (hmonoS : MonotoneOn f {r | r.val < S})
    (hboundR : BddBelow (f '' {r | r.val < R}))
    (hboundS : BddBelow (f '' {r | r.val < S})) :
    sInf (f '' {r | r.val < R}) = sInf (f '' {r | r.val < S}) :=
  tendsto_nhds_unique (tendsto_positive_atBot_csInf hR hmonoR hboundR)
    (tendsto_positive_atBot_csInf hS hmonoS hboundS)

end StratificationTheory
