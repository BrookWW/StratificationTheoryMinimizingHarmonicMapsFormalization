module

public import StratificationTheory.Foundation.DensityJointUpperSemicontinuity
public import StratificationTheory.Frozen.RegularDensity

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory

/-- Positive density superlevels and singular points persist at moving centers
for the actual prescribed weak local L2 limit of the original minimizing sequence. -/
theorem exists_prescribed_weak_limit_density_persistence {n q : ℕ} (hn : 2 ≤ n)
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
      (∀ (a : Ω.val) (y : ℕ → Ω.val),
        Tendsto (fun k => (y k).val) atTop (𝓝 a.val) →
        ∀ α : ℝ, 0 < α →
          (∀ᶠ k in atTop, α < density hn (hMinimizer k) (hu k) (hTarget k) (y k)) →
          α ≤ density hn hMinV hv hTv a) ∧
      ∀ (a : Ω.val) (y : ℕ → Ω.val),
        Tendsto (fun k => (y k).val) atTop (𝓝 a.val) →
        (∀ᶠ k in atTop, y k ∈ singularSet Ω (u k)) → a ∈ singularSet Ω v := by
  obtain ⟨Dv, hv, hTv, hMinV, _hWhole, hBallEnergy, _hJoint⟩ :=
    exists_prescribed_weak_limit_density_joint_upper_bound hn N Ω u Du v hu hTarget hMinimizer
      hEnergy hvL2 hWeakMap
  have hLower (a : Ω.val) (y : ℕ → Ω.val)
      (hy : Tendsto (fun k => (y k).val) atTop (𝓝 a.val)) (α : ℝ)
      (hα : ∀ᶠ k in atTop, α ≤ density hn (hMinimizer k) (hu k) (hTarget k) (y k)) :
      α ≤ density hn hMinV hv hTv a := by
    by_contra hnot
    have hGap : 0 < α - density hn hMinV hv hTv a := sub_pos.mpr (lt_of_not_ge hnot)
    have hUpper := (density_joint_upper_bound_of_ball_energy_convergence hn N Ω u Du v Dv
      hu hTarget hMinimizer hv hTv hMinV hBallEnergy a y hy).1
      ((α - density hn hMinV hv hTv a) / 2) (half_pos hGap)
    obtain ⟨k, hLowK, hUpK⟩ := (hα.and hUpper).exists
    linarith
  refine ⟨Dv, hv, hTv, hMinV, ?_, ?_⟩
  · intro a y hy α _hα hStrict
    exact hLower a y hy α (hStrict.mono fun _ hk => hk.le)
  · intro a y hy hSingular
    obtain ⟨τ, hτ, hCharacterization⟩ := regularPoint_density_characterization hn N
    have hLow : τ ≤ density hn hMinV hv hTv a := hLower a y hy τ
      (hSingular.mono fun k hk => (hCharacterization Ω (u k) (Du k)
        (hMinimizer k) (hu k) (hTarget k) (y k)).2 hk)
    change ¬ IsRegularPoint Ω v a
    intro hRegular
    have hZero := (hCharacterization Ω v Dv hMinV hv hTv a).1.mp hRegular
    rw [hZero] at hLow
    exact (not_le_of_gt hτ) hLow

end StratificationTheory
