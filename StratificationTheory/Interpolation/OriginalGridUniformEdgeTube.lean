module
public import StratificationTheory.Interpolation.OriginalGridNearLevelChannels
public import StratificationTheory.Foundation.OriginalCoordinateLineChannels

/-!
# Uniform original-edge tubes from one globally selected grid

Each original real edge energy and discrepancy is dominated by its actual
native channel and then by the global sampled channel on that same offset.
The resulting uniform tube coefficient has the frozen ambient powers.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

private theorem uniform_real_edge_tube_scale {ε K A D X Y : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hD : 0 ≤ D) (hX : 0 ≤ X)
    (hAX : X ≤ K * A) (hDY : Y ≤ K * D) :
    Y / ε + Real.sqrt (2 * Y * X) ≤ K * (D / ε + Real.sqrt (2 * D * A)) := by
  have hProd : 2 * Y * X ≤ K ^ 2 * (2 * D * A) := by
    calc
      _ ≤ 2 * (K * D) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDY (by norm_num)) hX
      _ ≤ 2 * (K * D) * (K * A) :=
        mul_le_mul_of_nonneg_left hAX (mul_nonneg (by norm_num) (mul_nonneg hK hD))
      _ = _ := by ring
  calc
    _ ≤ (K * D) / ε + Real.sqrt (K ^ 2 * (2 * D * A)) :=
      add_le_add (div_le_div_of_nonneg_right hDY hε.le) (Real.sqrt_le_sqrt hProd)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
      ring

/-- The original selected global native channels bound the real scalar
tube of every ball-contained original edge on that same fixed lattice.
This comparison alone does not assert Sobolev or integrability data. -/
theorem original_selected_grid_uniform_raw_edge_tube {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε : ℝ} (hε : 0 < ε) (count : ℕ) (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let C := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Eline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Eraw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let Dline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Draw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    (∀ k, (∑' z : L, Eline k z) ≤ c * ENNReal.ofReal A₀) →
    (∀ k, (∑' z : L, Dline k z) ≤ c * ENNReal.ofReal D₀) →
    ∀ (z : L) (normal : Fin (n + 2)),
      (∀ s ∈ Ioo (0 : ℝ) ε, y z + s • EuclideanSpace.single normal (1 : ℝ) ∈
        ball (0 : Domain (n + 2)) ((n : ℝ) + 3)) →
      let A := ∫ s in Ioo (0 : ℝ) ε,
        ‖Dw 0 (y z + s • EuclideanSpace.single normal (1 : ℝ)) normal‖ ^ 2 +
          ‖Dw 1 (y z + s • EuclideanSpace.single normal (1 : ℝ)) normal‖ ^ 2
      let D := ∫ s in Ioo (0 : ℝ) ε,
        ‖w 0 (y z + s • EuclideanSpace.single normal (1 : ℝ)) -
          w 1 (y z + s • EuclideanSpace.single normal (1 : ℝ))‖ ^ 2
      D / ε + Real.sqrt (2 * D * A) ≤ c.toReal * (D₀ / ε + Real.sqrt (2 * D₀ * A₀)) := by
  intro grid L y C Eraw Draw Eline Dline A₀ D₀ c hSelectE hSelectD z normal hImage A D
  have hc : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hε _)).ne'))
      (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top)
  have hA₀ : 0 ≤ A₀ := add_nonneg (integral_nonneg fun _ => hsNormSq_nonneg _)
    (integral_nonneg fun _ => hsNormSq_nonneg _)
  have hD₀ : 0 ≤ D₀ := integral_nonneg fun _ => sq_nonneg _
  have hA : 0 ≤ A := integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD : 0 ≤ D := integral_nonneg fun _ => sq_nonneg _
  have hAE : ENNReal.ofReal A ≤ c * ENNReal.ofReal A₀ := by
    exact (original_real_edge_combined_energy_le_native_channel (y z) normal Dw hImage).trans
      ((ENNReal.le_tsum z).trans (hSelectE normal))
  have hDE : ENNReal.ofReal D ≤ c * ENNReal.ofReal D₀ := by
    exact (original_real_edge_discrepancy_le_native_channel (y z) normal w hImage).trans
      ((ENNReal.le_tsum z).trans (hSelectD normal))
  have hAR : A ≤ c.toReal * A₀ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top) hAE
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hA₀] using h
  have hDR : D ≤ c.toReal * D₀ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top) hDE
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD, ENNReal.toReal_ofReal hD₀] using h
  exact uniform_real_edge_tube_scale hε ENNReal.toReal_nonneg hD₀ hA hAR hDR

end StratificationTheory
