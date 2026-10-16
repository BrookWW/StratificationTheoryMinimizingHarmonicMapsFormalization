module

public import StratificationTheory.Compactness.GeneralLimitEnergy
public import StratificationTheory.Interpolation.CompetitorExtension

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- Every admissible finite Sobolev competitor for the actual weak
limit is compared using its original zero-boundary difference. The limit is
therefore locally energy minimizing. -/
theorem limit_isLocallyEnergyMinimizing {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k)) (hv : MemW12Loc Ω v Dv)
    (huN : ∀ k, TakesValuesIn N Ω (u k)) (hvN : TakesValuesIn N Ω v)
    (hmin : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (ball a r) ≤ C)
    (hmap : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict K)) atTop (𝓝 0))
    (hweak : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
        Tendsto (fun k => ∫ x in K, inner ℝ (Du k x i) (w x)) atTop
          (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x)))) :
    IsLocallyEnergyMinimizing N Ω v Dv := by
  classical
  have hBallConv := ball_energy_tendsto_of_local_weak_limit
    hn N Ω u Du v Dv hu hv huN hvN hmin hEnergy hmap hweak
  intro c s hs hclosed w Dw hw hwN hboundary
  have hvI : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c s) :=
    hv.integrable_hsNormSq_ball hclosed
  have hwI : IntegrableOn (fun x => hsNormSq (Dw x)) (ball c s) := hw.integrable_hsNormSq
  apply (ENNReal.toReal_le_toReal (hv.dirichletEnergy_ne_top_ball hclosed)
    hw.dirichletEnergy_ne_top).mp
  change (dirichletEnergy Dv (ball c s)).toReal ≤ (dirichletEnergy Dw (ball c s)).toReal
  rw [dirichletEnergy_toReal hvI, dirichletEnergy_toReal hwI]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T, hsT, hclosedT⟩ := exists_larger_closedBall_in_openDomain Ω c hs.le hclosed
  have hT : 0 < T := hs.trans hsT
  have hvNT : TakesValuesIn N (ballDomain c T) v :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hclosedT) hvN
  obtain ⟨f, Df, hfEq, hDfEq, hfW, hfN, _hfzero⟩ :=
    Interpolation.extend_zeroBoundary_competitor_ball N hsT.le
      (hv.memW12_ball hclosedT) hvNT hwN hboundary
  have hinner : (∫ x in ball c s, hsNormSq (Df x)) =
      ∫ x in ball c s, hsNormSq (Dw x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [hDfEq, piecewise_eq_of_mem (ball c s) Dw Dv hx]
  obtain ⟨t, hst, htT, hEf⟩ := exists_larger_radius_integral_hsNormSq_lt
    (by omega : 0 < n) hs hsT (by positivity : 0 < ε / 2) hfW
  rw [hinner] at hEf
  obtain ⟨C, hC⟩ := hEnergy c T hT hclosedT
  have hDiffV : Tendsto (fun k => ∫ x in ball c t \ ball c s, ‖u k x - v x‖ ^ 2)
      atTop (𝓝 0) :=
    tendsto_integral_square_discrepancy_on_subset
      (fun k => (hu k).2.1 (closedBall c T) (isCompact_closedBall c T) hclosedT)
      (hv.2.1 (closedBall c T) (isCompact_closedBall c T) hclosedT)
      (sdiff_subset.trans ((ball_subset_ball htT.le).trans ball_subset_closedBall))
      (hmap (closedBall c T) (isCompact_closedBall c T) hclosedT)
  have hDiff : Tendsto (fun k => ∫ x in ball c t \ ball c s, ‖u k x - f x‖ ^ 2)
      atTop (𝓝 0) := by
    have heq (k : ℕ) : (∫ x in ball c t \ ball c s, ‖u k x - f x‖ ^ 2) =
        ∫ x in ball c t \ ball c s, ‖u k x - v x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with x hx
      rw [hfEq, piecewise_eq_of_notMem (ball c s) w v hx.2]
    simpa only [heq] using hDiffV
  have hcmp := eventually_minimizer_energy_comparison hn N Ω u Du f Df c
    hs hst htT hclosedT (fun k => (hu k).memW12_ball hclosedT) hfW
    (fun k => ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hclosedT) (huN k))
    hfN hmin C hC hDiff (ε / 2) (by positivity)
  apply le_of_tendsto (hBallConv c s hs hclosed)
  filter_upwards [hcmp] with k hk
  linarith only [hk, hEf]

end StratificationTheory.Compactness
