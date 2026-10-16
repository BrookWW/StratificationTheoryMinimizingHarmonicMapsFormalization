module

public import StratificationTheory.Compactness.PrescribedWeakLimitCompactness
public import StratificationTheory.Foundation.DensityJointEnergyBound

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Providers.DensityJointUpperSemicontinuity

/-- The prescribed weak local L2 map limit has genuine minimizing Sobolev
and strong whole-sequence data, and its named density bounds the moving-center
limsup along the original sequence. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (v : Domain n → Ambient q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hMinimizer : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (ball a r) ≤ C)
    (hvL2 : LocallyMemL2 Ω v)
    (hWeakMap : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      ∀ w : Lp (Ambient q) 2 (volume.restrict K),
        Tendsto (fun k => ∫ x in K, inner ℝ (u k x) (w x)) atTop
          (𝓝 (∫ x in K, inner ℝ (v x) (w x)))) :
    ∃ (Dv : Domain n → Gradient n q) (hv : MemW12Loc Ω v Dv)
      (hTv : TakesValuesIn N Ω v) (hMinV : IsLocallyEnergyMinimizing N Ω v Dv),
      (∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => Du k x i - Dv x i)
          2 (volume.restrict K)) atTop (𝓝 0)) ∧
      (∀ (c : Domain n) (r : ℝ), 0 < r → closedBall c r ⊆ Ω.val →
        Tendsto (fun k => ∫ x in ball c r, hsNormSq (Du k x)) atTop
          (𝓝 (∫ x in ball c r, hsNormSq (Dv x)))) ∧
      ∀ (a : Ω.val) (y : ℕ → Ω.val),
        Tendsto (fun k => (y k).val) atTop (𝓝 a.val) →
        Filter.limsup (fun k => density hn (hMinimizer k) (hu k) (hTarget k) (y k)) atTop ≤
          density hn hMinV hv hTv a := by
  obtain ⟨Dv, hv, hTv, hMinV, hWhole, hBallEnergy⟩ :=
    StratificationTheory.Compactness.exists_prescribed_weak_local_limit_data hn N Ω u Du v hu hTarget hMinimizer
      hEnergy hvL2 hWeakMap
  refine ⟨Dv, hv, hTv, hMinV, hWhole, hBallEnergy, ?_⟩
  intro a y hy
  exact (density_joint_upper_bound_of_ball_energy_convergence hn N Ω u Du v Dv
    hu hTarget hMinimizer hv hTv hMinV hBallEnergy a y hy).2

end StratificationTheory.Providers.DensityJointUpperSemicontinuity
