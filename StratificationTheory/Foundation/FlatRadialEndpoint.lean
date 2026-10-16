module

public import StratificationTheory.Foundation.LocalFlatRadialEndpoint
public import StratificationTheory.Foundation.CubicalConeGeometry

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- Equality on every strictly smaller maximum-coordinate cube gives
almost-everywhere equality on the actual open unit cube. -/
theorem ae_eq_unit_cube_of_smaller_cubes {n : ℕ} {E : Type*}
    (f g : Domain n → E)
    (h : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      f =ᵐ[volume.restrict {x : Domain n | ‖WithLp.ofLp x‖ < ρ}] g) :
    f =ᵐ[volume.restrict (⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1)] g := by
  have hc : Continuous (fun x : Domain n => ‖WithLp.ofLp x‖) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).norm
  have hEach (r : ℚ) : ∀ᵐ x : Domain n ∂volume,
      0 < (r : ℝ) → (r : ℝ) < 1 → ‖WithLp.ofLp x‖ < (r : ℝ) → f x = g x := by
    by_cases hr : 0 < (r : ℝ) ∧ (r : ℝ) < 1
    · have hImp := (ae_restrict_iff' (isOpen_lt hc continuous_const).measurableSet).mp (h r hr.1 hr.2)
      filter_upwards [hImp] with x hx _ _ hxNorm
      exact hx hxNorm
    · exact Eventually.of_forall fun _ hp h1 => False.elim (hr ⟨hp, h1⟩)
  have hB : MeasurableSet (⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1) :=
    MeasurableSet.iInter fun k => measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable
  filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hEach), ae_restrict_mem hB] with x hx hxB
  have hx1 : ‖WithLp.ofLp x‖ < 1 := by
    rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simpa only [Real.norm_eq_abs] using (mem_unit_coordinate_face_iff x).mp hxB
  obtain ⟨r, hxr, hr1⟩ := exists_rat_btwn hx1
  exact hx r ((norm_nonneg _).trans_lt hxr) hr1 hxr

/-- Local inverse-dilation identities identify the full native L2 endpoint
class on the entire original face, including points near its edges. -/
theorem continuous_flat_trace_endpoint_of_radial_slices {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) (F : Domain n × ℝ → E) :
    let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    ∀ hf : MemLp f 2 (volume.restrict B),
    ∀ H : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 (volume.restrict B),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t))) →
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Domain n, ‖WithLp.ofLp x‖ < t →
      F (x, t) = f (t⁻¹ • x)) →
    H ⟨1, by norm_num, le_rfl⟩ = hf.toLp f := by
  intro B hf H hH hFormula
  apply Lp.ext
  apply (ae_eq_unit_cube_of_smaller_cubes _ _ ?_).trans hf.coeFn_toLp.symm
  intro ρ hρ hρ1
  let U := {x : Domain n | ‖WithLp.ofLp x‖ < ρ}
  have hc : Continuous (fun x : Domain n => ‖WithLp.ofLp x‖) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).norm
  have hU : MeasurableSet U := (isOpen_lt hc continuous_const).measurableSet
  have hB : MeasurableSet B := MeasurableSet.iInter fun k =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable
  have hUS : U ⊆ B := by
    intro x hx
    apply (mem_unit_coordinate_face_iff x).mpr
    intro k
    have hk := norm_le_pi_norm (WithLp.ofLp x) k
    change |x k| ≤ ‖WithLp.ofLp x‖ at hk
    exact hk.trans_lt (hx.trans hρ1)
  apply continuous_flat_trace_endpoint_on_radial_subface hB hU hUS
    (by linarith : (-1 : ℝ) ≤ ρ) hρ hρ1 f hf F H hH
  · intro t x hx
    apply (mem_unit_coordinate_face_iff _).mpr
    intro k
    have ht : 0 < t.val := hρ.trans_le t.property.1
    have hk := norm_le_pi_norm (WithLp.ofLp x) k
    change |x k| ≤ ‖WithLp.ofLp x‖ at hk
    have hxt : |x k| < t.val := hk.trans_lt (hx.trans_le t.property.1)
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos ht]
    exact (inv_mul_lt_iff₀ ht).mpr (by simpa using hxt)
  · intro t ht x hx
    exact hFormula t ⟨hρ.trans ht.1, ht.2⟩ x (hx.trans ht.1)

end StratificationTheory
