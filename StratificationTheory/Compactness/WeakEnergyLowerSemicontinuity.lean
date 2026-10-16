module

public import StratificationTheory.Compactness.GradientHilbertIdentities
public import StratificationTheory.Compactness.HilbertLowerSemicontinuity

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StratificationTheory.Compactness

/-- Weak convergence of every actual gradient column gives lower
semicontinuity of the extended HS Dirichlet energy on the same region. -/
theorem dirichletEnergy_le_liminf_of_weak_columns {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict U)),
      Tendsto (fun k => ∫ x in U, inner ℝ (D k x i) (w x)) atTop
        (𝓝 (∫ x in U, inner ℝ (Dv x i) (w x)))) :
    dirichletEnergy Dv U ≤ atTop.liminf (fun k => dirichletEnergy (D k) U) := by
  have h := norm_sq_le_liminf_of_inner_tendsto
    (gradient_L2_product_pairing_tendsto hD hDv hweak)
  simpa only [gradient_L2_product_ofReal_norm_sq_eq_energy] using h

/-- At every positive tolerance, the limit energy is eventually bounded above
by the sequence energy plus that tolerance. All real energies are finite
because the actual columns lie in L2. -/
theorem eventually_dirichletEnergy_lower_bound_of_weak_columns {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict U)),
      Tendsto (fun k => ∫ x in U, inner ℝ (D k x i) (w x)) atTop
        (𝓝 (∫ x in U, inner ℝ (Dv x i) (w x))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (dirichletEnergy Dv U).toReal ≤
      (dirichletEnergy (D k) U).toReal + ε := by
  have h := eventually_norm_sq_lower_bound_of_inner_tendsto
    (gradient_L2_product_pairing_tendsto hD hDv hweak) hε
  simpa only [gradient_L2_product_norm_sq_eq_energy] using h

end StratificationTheory.Compactness
