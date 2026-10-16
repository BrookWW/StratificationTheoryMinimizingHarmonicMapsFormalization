module

public import StratificationTheory.Compactness.EnergyColumnBounds
public import StratificationTheory.Compactness.HilbertWeakSubsequence
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Simultaneous weak extraction of explicit gradient columns

The finite family of L2 classes is placed in the `PiLp 2` Hilbert product.
Its squared norm is the actual Hilbert--Schmidt Dirichlet energy. A single
subsequence therefore converges weakly in every displayed gradient column.
The weak limits here are L2 classes; distributional derivative identification
is a separate Sobolev closure result.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators

namespace StratificationTheory.Compactness

/-- A uniform HS energy bound on a Euclidean ball supplies one subsequence
for all actual gradient columns and preserves their total squared L2 bound. -/
theorem exists_weakly_convergent_gradient_subsequence_ball {n q : ℕ}
    (a : Domain n) (r : ℝ) (Du : ℕ → Domain n → Gradient n q)
    (hDu : ∀ k (i : Fin n), MemLp (fun x => Du k x i) 2
      (volume.restrict (Metric.ball a r)))
    (C : ℝ≥0)
    (hEnergy : ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ)
      (G : Fin n → Lp (Ambient q) 2 (volume.restrict (Metric.ball a r))),
      StrictMono κ ∧ (∑ i : Fin n, ‖G i‖ ^ 2) ≤ C ∧
      ∀ (i : Fin n) (v : Lp (Ambient q) 2 (volume.restrict (Metric.ball a r))),
        Tendsto (fun k => inner ℝ ((hDu (κ k) i).toLp (fun x => Du (κ k) x i)) v)
          atTop (𝓝 (inner ℝ (G i) v)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let H : Type := Lp (Ambient q) 2 (volume.restrict (Metric.ball a r))
  let f : ℕ → PiLp 2 (fun _ : Fin n => H) := fun k =>
    WithLp.toLp 2 (fun i => (hDu k i).toLp (fun x => Du k x i))
  have hnorm (k : ℕ) : ‖f k‖ ^ 2 =
      (dirichletEnergy (Du k) (Metric.ball a r)).toReal := by
    rw [PiLp.norm_sq_eq_of_L2]
    dsimp only [f, H, PiLp.toLp_apply]
    simp only [Lp.norm_toLp]
    exact sum_column_L2_norm_sq_eq_dirichletEnergy (hDu k)
  have hbound (k : ℕ) : ‖f k‖ ≤ Real.sqrt C := by
    apply Real.le_sqrt_of_sq_le
    rw [hnorm]
    have h := ENNReal.toReal_mono (by simp : (C : ℝ≥0∞) ≠ ∞) (hEnergy k)
    simpa only [ENNReal.coe_toReal] using h
  obtain ⟨κ, G, hκ, hG, hconv⟩ := exists_weakly_convergent_subsequence f (Real.sqrt C) hbound
  refine ⟨κ, (fun i => G i), hκ, ?_, ?_⟩
  · rw [← PiLp.norm_sq_eq_of_L2]
    have hsq := pow_le_pow_left₀ (norm_nonneg G) hG 2
    rw [Real.sq_sqrt (show 0 ≤ (C : ℝ) from C.property)] at hsq
    exact hsq
  · intro i v
    have hsingle (x : PiLp 2 (fun _ : Fin n => H)) :
        inner ℝ x (PiLp.single 2 i v) = inner ℝ (x i) v := by
      simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]
    have hv := hconv (PiLp.single 2 i v)
    simpa only [hsingle, f, PiLp.toLp_apply] using hv

/-- The simultaneous weak limit can be represented by one actual gradient
field, with finite energy and weak integral pairings for every column. This
result does not assert a distributional derivative identity. -/
theorem exists_weakly_convergent_gradient_field_ball {n q : ℕ}
    (a : Domain n) (r : ℝ) (Du : ℕ → Domain n → Gradient n q)
    (hDu : ∀ k (i : Fin n), MemLp (fun x => Du k x i) 2
      (volume.restrict (Metric.ball a r)))
    (C : ℝ≥0)
    (hEnergy : ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (Dv : Domain n → Gradient n q),
      StrictMono κ ∧
      (∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict (Metric.ball a r))) ∧
      dirichletEnergy Dv (Metric.ball a r) ≤ C ∧
      ∀ (i : Fin n) (v : Lp (Ambient q) 2 (volume.restrict (Metric.ball a r))),
        Tendsto (fun k => ∫ x in Metric.ball a r, inner ℝ (Du (κ k) x i) (v x))
          atTop (𝓝 (∫ x in Metric.ball a r, inner ℝ (Dv x i) (v x))) := by
  obtain ⟨κ, G, hκ, hG, hconv⟩ :=
    exists_weakly_convergent_gradient_subsequence_ball a r Du hDu C hEnergy
  let Dv : Domain n → Gradient n q := fun x i => G i x
  have hDv (i : Fin n) : MemLp (fun x => Dv x i) 2
      (volume.restrict (Metric.ball a r)) := Lp.memLp (G i)
  have hsum : (∑ i : Fin n,
      (eLpNorm (fun x => Dv x i) 2 (volume.restrict (Metric.ball a r))).toReal ^ 2) =
      ∑ i : Fin n, ‖G i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Lp.norm_toLp (fun x => Dv x i) (hDv i)]
    dsimp only [Dv]
    rw [Lp.toLp_coeFn]
  refine ⟨κ, Dv, hκ, hDv, ?_, ?_⟩
  · apply (ENNReal.toReal_le_toReal
      (dirichletEnergy_ne_top_of_integrable (integrable_hsNormSq_of_memLp_columns hDv))
      (by simp : (C : ℝ≥0∞) ≠ ∞)).mp
    simpa only [ENNReal.coe_toReal, ← sum_column_L2_norm_sq_eq_dirichletEnergy hDv,
      hsum] using hG
  · intro i v
    have heq (k : ℕ) :
        inner ℝ ((hDu (κ k) i).toLp (fun x => Du (κ k) x i)) v =
          ∫ x in Metric.ball a r, inner ℝ (Du (κ k) x i) (v x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hDu (κ k) i).coeFn_toLp] with x hx
      rw [hx]
    simpa only [heq, L2.inner_def, Dv] using hconv i v

end StratificationTheory.Compactness
