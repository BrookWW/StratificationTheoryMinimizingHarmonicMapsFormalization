module

public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.Analysis.VariableMollificationL2

public section

open HarmonicMaps MeasureTheory
open scoped ENNReal BigOperators

namespace StratificationTheory.Compactness

/-- Each actual gradient column's squared L2 norm is bounded by the finite
Hilbert--Schmidt Dirichlet energy on the same region. -/
theorem column_L2_norm_sq_le_dirichletEnergy {n q : ℕ}
    {Du : Domain n → Gradient n q} {U : Set (Domain n)}
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict U))
    (i : Fin n) :
    (eLpNorm (fun x => Du x i) 2 (volume.restrict U)).toReal ^ 2 ≤
      (dirichletEnergy Du U).toReal := by
  rw [← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hDu i),
    dirichletEnergy_toReal (integrable_hsNormSq_of_memLp_columns hDu)]
  exact integral_mono ((hDu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    (integrable_hsNormSq_of_memLp_columns hDu)
    (fun x => Finset.single_le_sum (fun j _ => sq_nonneg ‖Du x j‖) (Finset.mem_univ i))

/-- The finite-column L2 sum is exactly the finite Hilbert--Schmidt energy. -/
theorem sum_column_L2_norm_sq_eq_dirichletEnergy {n q : ℕ}
    {Du : Domain n → Gradient n q} {U : Set (Domain n)}
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict U)) :
    (∑ i : Fin n, (eLpNorm (fun x => Du x i) 2 (volume.restrict U)).toReal ^ 2) =
      (dirichletEnergy Du U).toReal := by
  rw [dirichletEnergy_toReal (integrable_hsNormSq_of_memLp_columns hDu)]
  simp_rw [← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hDu _)]
  exact (integral_finsetSum Finset.univ
    (fun i _ => (hDu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))).symm

end StratificationTheory.Compactness
