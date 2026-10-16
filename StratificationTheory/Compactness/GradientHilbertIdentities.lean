module

public import StratificationTheory.Compactness.EnergyColumnBounds
public import Mathlib.MeasureTheory.Function.L2Space

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace StratificationTheory.Compactness

/-- The finite Hilbert product of actual column L2 classes has squared norm
exactly equal to the finite real HS Dirichlet energy. -/
theorem gradient_L2_product_norm_sq_eq_energy {n q : ℕ}
    {U : Set (Domain n)} {D : Domain n → Gradient n q}
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 (volume.restrict U)) :
    ‖(WithLp.toLp 2 (fun i => (hD i).toLp (fun x => D x i)) :
      PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)))‖ ^ 2 =
      (dirichletEnergy D U).toReal := by
  rw [PiLp.norm_sq_eq_of_L2]
  simpa only [PiLp.toLp_apply, Lp.norm_toLp] using sum_column_L2_norm_sq_eq_dirichletEnergy hD

/-- The Hilbert-product energy identity recovers the actual extended HS energy;
column L2 membership supplies the finiteness needed for `ofReal ∘ toReal`. -/
theorem gradient_L2_product_ofReal_norm_sq_eq_energy {n q : ℕ}
    {U : Set (Domain n)} {D : Domain n → Gradient n q}
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 (volume.restrict U)) :
    ENNReal.ofReal (‖(WithLp.toLp 2 (fun i => (hD i).toLp (fun x => D x i)) :
      PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)))‖ ^ 2) =
      dirichletEnergy D U := by
  rw [gradient_L2_product_norm_sq_eq_energy hD,
    ENNReal.ofReal_toReal (dirichletEnergy_ne_top_of_integrable (integrable_hsNormSq_of_memLp_columns hD))]

private theorem inner_toLp_eq_integral_test {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) (v : Lp E 2 μ) :
    inner ℝ (hf.toLp f) v = ∫ x, inner ℝ (f x) (v x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Actual weak column pairings give convergence of the Hilbert-product pairing
with the limit field. The finite sum uses every original column. -/
theorem gradient_L2_product_pairing_tendsto {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict U)),
      Tendsto (fun k => ∫ x in U, inner ℝ (D k x i) (w x)) atTop
        (𝓝 (∫ x in U, inner ℝ (Dv x i) (w x)))) :
    Tendsto (fun k => inner ℝ
      (WithLp.toLp 2 (fun i => (hD k i).toLp (fun x => D k x i)) :
        PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)))
      (WithLp.toLp 2 (fun i => (hDv i).toLp (fun x => Dv x i)))) atTop
      (𝓝 (inner ℝ
        (WithLp.toLp 2 (fun i => (hDv i).toLp (fun x => Dv x i)) :
          PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict U)))
        (WithLp.toLp 2 (fun i => (hDv i).toLp (fun x => Dv x i))))) := by
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    hweak i ((hDv i).toLp (fun x => Dv x i))
  simpa only [PiLp.inner_apply, PiLp.toLp_apply, inner_toLp_eq_integral_test] using hsum

end StratificationTheory.Compactness
