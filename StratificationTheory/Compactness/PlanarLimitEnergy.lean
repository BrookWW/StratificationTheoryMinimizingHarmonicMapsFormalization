module

public import StratificationTheory.Compactness.PlanarSequenceComparison
public import StratificationTheory.Compactness.LocalL2Discrepancy
public import StratificationTheory.Compactness.InteriorBallEnlargement
public import StratificationTheory.Compactness.WeakLimitEnergyBound
public import StratificationTheory.Compactness.NearBallEnergyRadius

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- A target-valued local weak limit of planar minimizers has the actual
ball-energy limit. The projected-circle comparison supplies the upper bound;
no convergence of energies or gradients is an input. -/
theorem planar_ball_energy_tendsto_of_local_weak_limit {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 2)
    (u : ℕ → Domain 2 → Ambient q) (Du : ℕ → Domain 2 → Gradient 2 q)
    (v : Domain 2 → Ambient q) (Dv : Domain 2 → Gradient 2 q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k)) (hv : MemW12Loc Ω v Dv)
    (huN : ∀ k, TakesValuesIn N Ω (u k)) (hvN : TakesValuesIn N Ω v)
    (hmin : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain 2) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (ball a r) ≤ C)
    (hmap : ∀ K : Set (Domain 2), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict K)) atTop (𝓝 0))
    (hweak : ∀ K : Set (Domain 2), IsCompact K → K ⊆ Ω.val →
      ∀ (i : Fin 2) (w : Lp (Ambient q) 2 (volume.restrict K)),
        Tendsto (fun k => ∫ x in K, inner ℝ (Du k x i) (w x)) atTop
          (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x)))) :
    ∀ (c : Domain 2) (s : ℝ), 0 < s → closedBall c s ⊆ Ω.val →
      Tendsto (fun k => ∫ x in ball c s, hsNormSq (Du k x)) atTop
        (𝓝 (∫ x in ball c s, hsNormSq (Dv x))) := by
  intro c s hs hclosed
  obtain ⟨T, hsT, hclosedT⟩ := exists_larger_closedBall_in_openDomain Ω c hs.le hclosed
  have hT : 0 < T := hs.trans hsT
  have hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ x in ball c s, hsNormSq (Du k x)) ≤
        (∫ x in ball c s, hsNormSq (Dv x)) + ε := by
    intro ε hε
    obtain ⟨t, hst, htT, hEv⟩ := exists_larger_radius_integral_hsNormSq_lt
      (by norm_num : 0 < 2) hs hsT (by positivity : 0 < ε / 2) (hv.memW12_ball hclosedT)
    obtain ⟨C, hC⟩ := hEnergy c T hT hclosedT
    have hDiff : Tendsto (fun k => ∫ x in ball c t \ ball c s, ‖u k x - v x‖ ^ 2)
        atTop (𝓝 0) :=
      tendsto_integral_square_discrepancy_on_subset
        (fun k => (hu k).2.1 (closedBall c T) (isCompact_closedBall c T) hclosedT)
        (hv.2.1 (closedBall c T) (isCompact_closedBall c T) hclosedT)
        (sdiff_subset.trans ((ball_subset_ball htT.le).trans ball_subset_closedBall))
        (hmap (closedBall c T) (isCompact_closedBall c T) hclosedT)
    have hcmp := eventually_planar_minimizer_energy_comparison N Ω u Du v Dv c
      hs hst htT hclosedT (fun k => (hu k).memW12_ball hclosedT)
      (hv.memW12_ball hclosedT)
      (fun k => ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hclosedT) (huN k))
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hclosedT) hvN)
      hmin C hC hDiff (ε / 2) (by positivity)
    filter_upwards [hcmp] with k hk
    linarith only [hk, hEv]
  have hDball (k : ℕ) (i : Fin 2) : MemLp (fun x => Du k x i) 2 (volume.restrict (ball c s)) :=
    ((hu k).memW12_ball hclosed).2.2 i
  have hDvball (i : Fin 2) : MemLp (fun x => Dv x i) 2 (volume.restrict (ball c s)) :=
    (hv.memW12_ball hclosed).2.2 i
  have hweakball (i : Fin 2) (w : Lp (Ambient q) 2 (volume.restrict (ball c s))) :
      Tendsto (fun k => ∫ x in ball c s, inner ℝ (Du k x i) (w x)) atTop
        (𝓝 (∫ x in ball c s, inner ℝ (Dv x i) (w x))) :=
    weak_L2_integral_convergence_mono measurableSet_ball ball_subset_closedBall
      (hweak (closedBall c s) (isCompact_closedBall c s) hclosed i) w
  have hIv : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c s) :=
    hv.integrable_hsNormSq_ball hclosed
  have hIu (k : ℕ) : IntegrableOn (fun x => hsNormSq (Du k x)) (ball c s) :=
    (hu k).integrable_hsNormSq_ball hclosed
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hLower := eventually_dirichletEnergy_lower_bound_of_weak_columns
    hDball hDvball hweakball (by positivity : 0 < ε / 2)
  simp only [dirichletEnergy_toReal hIv, dirichletEnergy_toReal (hIu _)] at hLower
  filter_upwards [hUpper (ε / 2) (by positivity), hLower] with k hU hL
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith only [hε, hU, hL]

end StratificationTheory.Compactness
