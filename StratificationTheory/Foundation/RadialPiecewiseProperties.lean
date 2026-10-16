module

public import StratificationTheory.Foundation.RadialPiecewiseSobolevData

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Any original almost-everywhere value property on the two open radial
pieces holds for their literal piecewise map on the larger ball. -/
theorem ae_radial_piecewise_property {n : ℕ} {E : Type*}
    (c : Domain n) {r R : ℝ} (hr : 0 < r) (_hrR : r < R)
    (u w : Domain n → E) (P : E → Prop)
    (hu : ∀ᵐ x ∂volume.restrict (ball c r), P (u x))
    (hw : ∀ᵐ x ∂volume.restrict {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R}, P (w x)) :
    ∀ᵐ x ∂volume.restrict (ball c R), P (if ‖x - c‖ < r then u x else w x) := by
  have hu' := (ae_restrict_iff' measurableSet_ball).mp hu
  have hw' := (ae_restrict_iff'
    (isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm).measurableSet).mp hw
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hu',
    ae_restrict_of_ae hw', ae_restrict_of_ae (ae_norm_sub_ne_radius c hr)] with x hx hux hwx hne
  by_cases hxr : ‖x - c‖ < r
  · rw [if_pos hxr]
    exact hux (mem_ball_iff_norm.mpr hxr)
  · rw [if_neg hxr]
    exact hwx ⟨lt_of_le_of_ne (le_of_not_gt hxr) (Ne.symm hne), mem_ball_iff_norm.mp hx⟩

end StratificationTheory
