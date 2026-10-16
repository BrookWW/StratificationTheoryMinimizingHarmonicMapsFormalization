module

public import StratificationTheory.Foundation.CubicalNearLevelLatticeIncidence

/-! # Pointwise edge-tube control from actual near-level window sums -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Every real finite-edge tube expression on a cell meeting the actual
cubical level is controlled by the two near-level sums on that same radius.
The comparison uses the actual cell window, rather than whole-grid maxima. -/
theorem finite_edge_tube_le_cubical_near_level_sums {n : ℕ} {G I : Type*}
    [AddGroup G] [Fintype I] {ε r : ℝ} (hε : 0 < ε)
    (origin : G → Domain n) (shift : I → G)
    (A D : I → G → ℝ≥0∞) (a d : I → G → ℝ)
    (ha : ∀ i z, 0 ≤ a i z) (hd : ∀ i z, 0 ≤ d i z)
    (hA : ∀ i z, ENNReal.ofReal (a i z) ≤ A i z)
    (hD : ∀ i z, ENNReal.ofReal (d i z) ≤ D i z) :
    let near := fun (weight : I → G → ℝ≥0∞) => ∑' z : G,
      (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => ∑ i : I, weight i (z + shift i)) r
    near A ≠ ⊤ → near D ≠ ⊤ →
    ∀ z : G,
    (∃ x : Domain n, (∀ j, x j - origin z j ∈ Icc (0 : ℝ) ε) ∧ ‖WithLp.ofLp x‖ = r) →
    (∑ i : I, (d i (z + shift i) / ε + Real.sqrt (2 * d i (z + shift i) * a i (z + shift i)))) ≤
      (Fintype.card I : ℝ) * ((near D).toReal / ε + Real.sqrt (2 * (near D).toReal * (near A).toReal)) := by
  intro near hAFinite hDFinite z hMeet
  have hWindow := cubical_level_intersect_cell_radius_window hε.le (origin z) hMeet
  have hPoint (weight : I → G → ℝ≥0∞) (i : I) : weight i (z + shift i) ≤ near weight := by
    calc
      _ ≤ ∑ j : I, weight j (z + shift j) :=
        Finset.single_le_sum (fun j _ => (zero_le : 0 ≤ weight j (z + shift j))) (Finset.mem_univ i)
      _ = (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
          (fun _ : ℝ => ∑ i : I, weight i (z + shift i)) r :=
        by rw [Set.indicator_of_mem hWindow]
      _ ≤ _ := ENNReal.le_tsum z
  have hAR (i : I) : a i (z + shift i) ≤ (near A).toReal := by
    have h := ENNReal.toReal_mono hAFinite ((hA i _).trans (hPoint A i))
    simpa only [ENNReal.toReal_ofReal (ha i _)] using h
  have hDR (i : I) : d i (z + shift i) ≤ (near D).toReal := by
    have h := ENNReal.toReal_mono hDFinite ((hD i _).trans (hPoint D i))
    simpa only [ENNReal.toReal_ofReal (hd i _)] using h
  have hOne (i : I) :
      d i (z + shift i) / ε + Real.sqrt (2 * d i (z + shift i) * a i (z + shift i)) ≤
        (near D).toReal / ε + Real.sqrt (2 * (near D).toReal * (near A).toReal) := by
    apply add_le_add (div_le_div_of_nonneg_right (hDR i) hε.le)
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ 2 * (near D).toReal * a i (z + shift i) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hDR i) (by norm_num)) (ha i _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hAR i) (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
  calc
    _ ≤ ∑ _i : I, ((near D).toReal / ε + Real.sqrt (2 * (near D).toReal * (near A).toReal)) :=
      Finset.sum_le_sum fun i _ => hOne i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end StratificationTheory
