module

public import HarmonicMaps.SobolevLemmas
public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual L2 and integral data for radial piecewise maps

The inner ball and open outer annulus partition the larger ball up to its
null interior sphere. The original piecewise maps therefore retain their
actual L2 columns and additive squared Hilbert--Schmidt integral.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- The splitting sphere has zero ambient volume, including in dimension zero
when its positive radius makes it empty. -/
theorem ae_norm_sub_ne_radius {n : ℕ} (c : Domain n) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x : Domain n ∂volume, ‖x - c‖ ≠ r := by
  have h : (volume : Measure (Domain n)) (sphere c r) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume c hr.ne'
  have ha := measure_eq_zero_iff_ae_notMem.mp h
  simpa only [mem_sphere_iff_norm, dist_eq_norm] using ha

/-- The original indicator of the piecewise map is the sum of the original
inner and outer indicators outside the null splitting sphere. -/
theorem radial_piecewise_indicator_ae {n : ℕ} {E : Type*} [AddZeroClass E]
    (c : Domain n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u w : Domain n → E) :
    (ball c R).indicator (fun x => if ‖x - c‖ < r then u x else w x) =ᵐ[volume]
      fun x => (ball c r).indicator u x +
        ({x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R}).indicator w x := by
  filter_upwards [ae_norm_sub_ne_radius c hr] with x hx
  by_cases hxr : ‖x - c‖ < r
  · have hxR : x ∈ ball c R := mem_ball_iff_norm.mpr (hxr.trans hrR)
    have hxin : x ∈ ball c r := mem_ball_iff_norm.mpr hxr
    have hxout : x ∉ {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R} :=
      fun h => (not_lt_of_ge hxr.le) h.1
    simp only [hxr, if_pos, indicator_of_mem hxR, indicator_of_mem hxin,
      indicator_of_notMem hxout, add_zero]
  · have hxgt : r < ‖x - c‖ := lt_of_le_of_ne (le_of_not_gt hxr) (Ne.symm hx)
    have hxnin : x ∉ ball c r := by simpa only [mem_ball_iff_norm] using hxr
    by_cases hxR : ‖x - c‖ < R
    · have hxinR : x ∈ ball c R := mem_ball_iff_norm.mpr hxR
      have hxout : x ∈ {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R} := ⟨hxgt, hxR⟩
      simp only [hxr, ↓reduceIte, indicator_of_mem hxinR, indicator_of_notMem hxnin,
        indicator_of_mem hxout, zero_add]
    · have hxnR : x ∉ ball c R := by simpa only [mem_ball_iff_norm] using hxR
      have hxout : x ∉ {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R} := fun h => hxR h.2
      simp only [indicator_of_notMem hxnR, indicator_of_notMem hxnin,
        indicator_of_notMem hxout, add_zero]

/-- Actual finite L2 membership for the literal original piecewise map. -/
theorem memLp_radial_piecewise {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (c : Domain n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u w : Domain n → E)
    (hu : MemLp u 2 (volume.restrict (ball c r)))
    (hw : MemLp w 2 (volume.restrict {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R})) :
    MemLp (fun x => if ‖x - c‖ < r then u x else w x) 2
      (volume.restrict (ball c R)) := by
  have hinner := (memLp_indicator_iff_restrict isOpen_ball.measurableSet).mpr hu
  have houter := (memLp_indicator_iff_restrict
    (isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm).measurableSet).mpr hw
  exact (memLp_indicator_iff_restrict isOpen_ball.measurableSet).mp
    ((hinner.add houter).ae_eq (radial_piecewise_indicator_ae c hr hrR u w).symm)

/-- The same literal split has the exact original additive Bochner integral. -/
theorem integral_radial_piecewise {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Domain n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u w : Domain n → E) (hu : IntegrableOn u (ball c r))
    (hw : IntegrableOn w {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R}) :
    (∫ x in ball c R, if ‖x - c‖ < r then u x else w x) =
      (∫ x in ball c r, u x) +
        (∫ x in {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R}, w x) := by
  have hs : MeasurableSet {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R} :=
    (isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm).measurableSet
  rw [← integral_indicator isOpen_ball.measurableSet,
    integral_congr_ae (radial_piecewise_indicator_ae c hr hrR u w),
    integral_add ((integrable_indicator_iff isOpen_ball.measurableSet).mpr hu)
      ((integrable_indicator_iff hs).mpr hw),
    integral_indicator isOpen_ball.measurableSet, integral_indicator hs]

/-- Actual original finite Sobolev data already give the piecewise L2 map,
all its piecewise columns, and the exact additive HS energy. Weak gluing is
a separate theorem and is not an input to this data lemma. -/
theorem radial_piecewise_sobolev_L2_energy {n q : ℕ}
    (c : Domain n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u w : Domain n → Ambient q) (Du Dw : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain c r) u Du)
    (hw : MemW12 ⟨{x | r < ‖x - c‖ ∧ ‖x - c‖ < R},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ w Dw) :
    MemLp (fun x => if ‖x - c‖ < r then u x else w x) 2
      (volume.restrict (ball c R)) ∧
    (∀ i, MemLp (fun x => if ‖x - c‖ < r then Du x i else Dw x i) 2
      (volume.restrict (ball c R))) ∧
    (∫ x in ball c R, hsNormSq (fun i => if ‖x - c‖ < r then Du x i else Dw x i)) =
      (∫ x in ball c r, hsNormSq (Du x)) +
        (∫ x in {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < R}, hsNormSq (Dw x)) := by
  refine ⟨memLp_radial_piecewise c hr hrR u w hu.2.1 hw.2.1,
    fun i => memLp_radial_piecewise c hr hrR _ _ (hu.2.2 i) (hw.2.2 i), ?_⟩
  have hsplit (x : Domain n) :
      hsNormSq (fun i => if ‖x - c‖ < r then Du x i else Dw x i) =
        if ‖x - c‖ < r then hsNormSq (Du x) else hsNormSq (Dw x) := by
    split_ifs <;> rfl
  simp_rw [hsplit]
  exact integral_radial_piecewise c hr hrR _ _
    (integrable_hsNormSq_of_memLp_columns hu.2.2)
    (integrable_hsNormSq_of_memLp_columns hw.2.2)

end StratificationTheory
