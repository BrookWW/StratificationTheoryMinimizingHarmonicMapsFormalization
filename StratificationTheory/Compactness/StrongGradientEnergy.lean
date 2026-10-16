module

public import StratificationTheory.Compactness.GradientHilbertIdentities
public import StratificationTheory.Compactness.GradientStrongConvergence

public section
open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace StratificationTheory.Compactness

/-- Strong convergence of every original L2 gradient column gives
convergence of the actual finite Hilbert--Schmidt energy integral. -/
theorem integral_hsNormSq_tendsto_of_strong_columns {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hStrong : ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Dv x i)
      2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in U, hsNormSq (D k x)) atTop
      (𝓝 (∫ x in U, hsNormSq (Dv x))) := by
  have hNorm (i : Fin n) : Tendsto (fun k =>
      (eLpNorm (fun x => D k x i) 2 (volume.restrict U)).toReal ^ 2) atTop
      (𝓝 ((eLpNorm (fun x => Dv x i) 2 (volume.restrict U)).toReal ^ 2)) := by
    have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k x => D k x i)
      (fun k => hD k i) (fun x => Dv x i) (hDv i)).mpr (hStrong i)
    simpa only [Lp.norm_toLp] using hLp.norm.pow 2
  have hSum := tendsto_finsetSum Finset.univ (fun i _ => hNorm i)
  simpa only [sum_column_L2_norm_sq_eq_dirichletEnergy (hD _),
    sum_column_L2_norm_sq_eq_dirichletEnergy hDv,
    dirichletEnergy_toReal (integrable_hsNormSq_of_memLp_columns (hD _)),
    dirichletEnergy_toReal (integrable_hsNormSq_of_memLp_columns hDv)] using hSum

/-- Strong convergence of the actual columns also gives convergence of the
extended nonnegative Dirichlet energies, with genuine finiteness supplied by L2. -/
theorem dirichletEnergy_tendsto_of_strong_columns {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hStrong : ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Dv x i)
      2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun k => dirichletEnergy (D k) U) atTop (𝓝 (dirichletEnergy Dv U)) := by
  have h := ENNReal.tendsto_ofReal (integral_hsNormSq_tendsto_of_strong_columns hD hDv hStrong)
  simpa only [dirichletEnergy_eq_ofReal_integral (integrable_hsNormSq_of_memLp_columns (hD _)),
    dirichletEnergy_eq_ofReal_integral (integrable_hsNormSq_of_memLp_columns hDv)] using h

/-- The actual extended Dirichlet energy of the same gradient difference
tends to zero under strong convergence of every original column. -/
theorem gradient_difference_energy_tendsto_zero_of_strong_columns {n q : ℕ}
    {U : Set (Domain n)} {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin n, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hStrong : ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Dv x i)
      2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun k => dirichletEnergy (fun x i => D k x i - Dv x i) U) atTop (𝓝 0) := by
  have hDiff (k : ℕ) (i : Fin n) : MemLp (fun x => D k x i - Dv x i) 2 (volume.restrict U) :=
    (hD k i).sub (hDv i)
  have h := ENNReal.tendsto_ofReal (tendsto_integral_hsNormSq_zero hDiff hStrong)
  simpa only [ENNReal.ofReal_zero,
    dirichletEnergy_eq_ofReal_integral (integrable_hsNormSq_of_memLp_columns (hDiff _))] using h

end StratificationTheory.Compactness
