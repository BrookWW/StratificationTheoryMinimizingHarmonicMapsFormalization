module

public import StratificationTheory.Foundation.CubicalNearLevelJointSelection

/-! # Near-level sums of actual finite translates of lattice channels -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Finite cell-incidence shifts preserve the complete lattice sums exactly. -/
theorem tsum_finite_lattice_shift_channels {G I : Type*} [AddGroup G] [Fintype I]
    (shift : I → G) (weight : I → G → ℝ≥0∞) :
    (∑' z : G, ∑ i : I, weight i (z + shift i)) = ∑ i : I, ∑' z : G, weight i z := by
  have hShift (i : I) : (∑' z : G, weight i (z + shift i)) = ∑' z : G, weight i z :=
    (Equiv.addRight (shift i)).tsum_eq (weight i)
  calc
    _ = ∑' z : G, ∑' i : I, weight i (z + shift i) := by simp only [tsum_fintype]
    _ = ∑' i : I, ∑' z : G, weight i (z + shift i) := ENNReal.tsum_comm
    _ = _ := by simp_rw [hShift]; rw [tsum_fintype]

/-- Integrating near-parent windows counts a finite family of actual lattice
shifts with exactly the width factor, independently of the shifts. -/
theorem lintegral_cubical_window_finite_shift_channels {n : ℕ} {G I : Type*}
    [AddGroup G] [Countable G] [Fintype I] {ε : ℝ}
    (origin : G → Domain n) (shift : I → G) (weight : I → G → ℝ≥0∞) :
    (∫⁻ r : ℝ, ∑' z : G,
      (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => ∑ i : I, weight i (z + shift i)) r) =
      ENNReal.ofReal (2 * ε) * ∑ i : I, ∑' z : G, weight i z := by
  rw [lintegral_cubical_cell_window_tsum, tsum_finite_lattice_shift_channels]

/-- One radius controls energy and both original finite shifted channels.
The input channels are whole-lattice scalar densities, not pointwise maxima
of individual cell weights. -/
theorem exists_joint_cubical_level_shift_channel_bounds {n : ℕ} {G I : Type*}
    [AddGroup G] [Countable G] [Fintype I] {a b ε : ℝ} (hab : a < b)
    (origin : G → Domain n) (shift : I → G) (A D : I → G → ℝ≥0∞)
    (hA : ∀ i, (∑' z : G, A i z) ≠ ⊤) (hD : ∀ i, (∑' z : G, D i z) ≠ ⊤)
    (energy : ℝ → ℝ≥0∞) (hEnergy : AEMeasurable energy (volume.restrict (Ioo a b)))
    (hEnergyFinite : (∫⁻ r in Ioo a b, energy r) ≠ ⊤)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Ioo a b), P r) :
    ∃ r ∈ Ioo a b, P r ∧
      energy r ≤ 3 * (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ s in Ioo a b, energy s ∧
      (∑' z : G, (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => ∑ i : I, A i (z + shift i)) r) ≤
          6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * ∑ i : I, ∑' z : G, A i z ∧
      (∑' z : G, (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => ∑ i : I, D i (z + shift i)) r) ≤
          6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * ∑ i : I, ∑' z : G, D i z := by
  have hAFinite : (∑' z : G, ∑ i : I, A i (z + shift i)) ≠ ⊤ := by
    rw [tsum_finite_lattice_shift_channels]
    exact ENNReal.sum_ne_top.mpr (fun i _ => hA i)
  have hDFinite : (∑' z : G, ∑ i : I, D i (z + shift i)) ≠ ⊤ := by
    rw [tsum_finite_lattice_shift_channels]
    exact ENNReal.sum_ne_top.mpr (fun i _ => hD i)
  obtain ⟨r, hr, hPr, hE, hA', hD'⟩ := exists_joint_cubical_level_window_bounds hab origin
    (fun z => ∑ i : I, A i (z + shift i)) (fun z => ∑ i : I, D i (z + shift i))
    hAFinite hDFinite energy hEnergy hEnergyFinite hP
  refine ⟨r, hr, hPr, hE, ?_, ?_⟩
  · simpa only [tsum_finite_lattice_shift_channels] using hA'
  · simpa only [tsum_finite_lattice_shift_channels] using hD'

end StratificationTheory
