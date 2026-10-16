module

public import StratificationTheory.Foundation.CubicalNearLevelSampling
public import StratificationTheory.Foundation.FiniteDensitySelection

/-! # One cubical level for energy, near-cell channels and an AE event -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- A single actual radius preserves the prescribed almost-everywhere event,
the energy mean bound, and both near-cell channels. The near-cell factor is
produced by integrating the actual radius windows, rather than assumed. -/
theorem exists_joint_cubical_level_window_bounds {n : ℕ} {Z : Type*} [Countable Z]
    {a b ε : ℝ} (hab : a < b) (origin : Z → Domain n)
    (A D : Z → ℝ≥0∞) (hA : (∑' z, A z) ≠ ⊤) (hD : (∑' z, D z) ≠ ⊤)
    (energy : ℝ → ℝ≥0∞) (hEnergy : AEMeasurable energy (volume.restrict (Ioo a b)))
    (hEnergyFinite : (∫⁻ r in Ioo a b, energy r) ≠ ⊤)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Ioo a b), P r) :
    ∃ r ∈ Ioo a b, P r ∧
      energy r ≤ 3 * (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ s in Ioo a b, energy s ∧
      (∑' z : Z, (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => A z) r) ≤
          6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * ∑' z : Z, A z ∧
      (∑' z : Z, (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => D z) r) ≤
          6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * ∑' z : Z, D z := by
  let μ := (volume : Measure ℝ).restrict (Ioo a b)
  let win := fun (weight : Z → ℝ≥0∞) (r : ℝ) => ∑' z : Z,
    (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
      (fun _ : ℝ => weight z) r
  have hWindowMeas (weight : Z → ℝ≥0∞) : AEMeasurable (win weight) μ := by
    exact AEMeasurable.tsum fun z => (measurable_const.indicator measurableSet_Icc).aemeasurable
  have hWindowIntegral (weight : Z → ℝ≥0∞) :
      (∫⁻ r, win weight r ∂μ) ≤ ENNReal.ofReal (2 * ε) * ∑' z, weight z := by
    exact (setLIntegral_le_lintegral (Ioo a b) (win weight)).trans_eq
      (lintegral_cubical_cell_window_tsum origin weight)
  have hWindowFinite (weight : Z → ℝ≥0∞) (hWeight : (∑' z, weight z) ≠ ⊤) :
      (∫⁻ r, win weight r ∂μ) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWeight) (hWindowIntegral weight)
  have hμFinite : (volume : Measure ℝ) (Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hμFinite
  have hμ : μ ≠ 0 := by
    rw [ne_eq, Measure.restrict_eq_zero, Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hμUniv : μ univ = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  let f : Fin 3 → ℝ → ℝ≥0∞ := ![energy, win A, win D]
  have hf : ∀ j, AEMeasurable (f j) μ := by
    intro j
    fin_cases j
    · exact hEnergy
    · exact hWindowMeas A
    · exact hWindowMeas D
  have hfFinite : ∀ j, (∫⁻ r, f j r ∂μ) ≠ ⊤ := by
    intro j
    fin_cases j
    · exact hEnergyFinite
    · exact hWindowFinite A hA
    · exact hWindowFinite D hD
  have hEvent : ∀ᵐ r ∂μ, r ∈ Ioo a b ∧ P r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hP] with r hr hPr
    exact ⟨hr, hPr⟩
  obtain ⟨r, hr, hBounds⟩ := exists_joint_finite_density_le_mean hμ f hf hfFinite hEvent
  have hTwo : ENNReal.ofReal (2 * ε) = 2 * ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hWindowBound (weight : Z → ℝ≥0∞)
      (h : win weight r ≤ 3 * (μ univ)⁻¹ * ∫⁻ s, win weight s ∂μ) :
      win weight r ≤ 6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * ∑' z, weight z := by
    calc
      _ ≤ 3 * (μ univ)⁻¹ * (ENNReal.ofReal (2 * ε) * ∑' z, weight z) :=
        h.trans (mul_le_mul_right (hWindowIntegral weight) _)
      _ = _ := by rw [hμUniv, hTwo]; ring
  refine ⟨r, hr.1, hr.2, ?_, ?_, ?_⟩
  · simpa [f, hμUniv, μ] using hBounds 0
  · apply hWindowBound A
    simpa [f] using hBounds 1
  · apply hWindowBound D
    simpa [f] using hBounds 2

end StratificationTheory
