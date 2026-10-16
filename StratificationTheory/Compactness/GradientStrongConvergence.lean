module

public import StratificationTheory.Compactness.GradientHilbertIdentities
public import StratificationTheory.Compactness.HilbertStrongConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StratificationTheory.Compactness

/-- Actual weak column convergence and actual HS energy convergence on one
region imply strong L2 convergence of every original column. Energy convergence
is a condition of this ordinary Hilbert-space implication. -/
theorem gradient_columns_strong_of_weak_and_energy {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict U)),
      Tendsto (fun k => ∫ x in U, inner ℝ (D k x i) (w x)) atTop
        (𝓝 (∫ x in U, inner ℝ (Dv x i) (w x))))
    (hEnergy : Tendsto (fun k => (dirichletEnergy (D k) U).toReal) atTop
      (𝓝 (dirichletEnergy Dv U).toReal)) :
    ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Dv x i)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun k =>
      ‖(WithLp.toLp 2 (fun i => (hD k i).toLp (fun x => D k x i)) :
        PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)))‖ ^ 2)
      atTop (𝓝 (‖(WithLp.toLp 2 (fun i => (hDv i).toLp (fun x => Dv x i)) :
        PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)))‖ ^ 2)) := by
    simpa only [gradient_L2_product_norm_sq_eq_energy] using hEnergy
  have hstrong := tendsto_of_norm_sq_and_inner hnorm
    (gradient_L2_product_pairing_tendsto hD hDv hweak)
  intro i
  have hcol := (PiLp.continuous_apply (p := (2 : ℝ≥0∞))
    (β := fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)) i).tendsto
      (WithLp.toLp 2 (fun j => (hDv j).toLp (fun x => Dv x j))) |>.comp hstrong
  have hcol' : Tendsto (fun k => (hD k i).toLp (fun x => D k x i)) atTop
      (𝓝 ((hDv i).toLp (fun x => Dv x i))) := by
    simpa only [Function.comp_def, PiLp.toLp_apply] using hcol
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k x => D k x i)
    (fun k => hD k i) (fun x => Dv x i) (hDv i)).mp hcol'


/-- Under the same weak and energy convergence, the actual HS Dirichlet
energy of the gradient difference tends to zero. -/
theorem gradient_difference_energy_tendsto_zero_of_weak_and_energy {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict U)),
      Tendsto (fun k => ∫ x in U, inner ℝ (D k x i) (w x)) atTop
        (𝓝 (∫ x in U, inner ℝ (Dv x i) (w x))))
    (hEnergy : Tendsto (fun k => (dirichletEnergy (D k) U).toReal) atTop
      (𝓝 (dirichletEnergy Dv U).toReal)) :
    Tendsto (fun k => dirichletEnergy (fun x i => D k x i - Dv x i) U)
      atTop (𝓝 0) := by
  have hDiff : ∀ k (i : Fin n), MemLp (fun x => D k x i - Dv x i) 2 (volume.restrict U) :=
    fun k i => (hD k i).sub (hDv i)
  have hcol := gradient_columns_strong_of_weak_and_energy hD hDv hweak hEnergy
  have hint := tendsto_integral_hsNormSq_zero hDiff hcol
  have h := ENNReal.tendsto_ofReal hint
  have heq (k : ℕ) := dirichletEnergy_eq_ofReal_integral
    (integrable_hsNormSq_of_memLp_columns (hDiff k))
  simpa only [ENNReal.ofReal_zero, ← heq] using h

end StratificationTheory.Compactness
