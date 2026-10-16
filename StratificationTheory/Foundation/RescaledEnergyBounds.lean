module

public import StratificationTheory.Foundation.NormalizedEnergyOrder
public import StratificationTheory.Foundation.PositiveRadiusLimits

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HarmonicMaps

/-- Positive radii permit the exact inverse normalization, including for
extended Dirichlet energies. -/
theorem dirichletEnergy_ball_eq_mul_normalizedEnergy {n q : ℕ}
    (Du : Domain n → Gradient n q) (a : Domain n) (r : PositiveRadius) :
    dirichletEnergy Du (Metric.ball a r.val) =
      ENNReal.ofReal (r.val ^ ((n : ℤ) - 2)) * normalizedEnergy Du a r := by
  unfold normalizedEnergy
  rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (zpow_pos r.property _))]
  have hpower : r.val ^ ((n : ℤ) - 2) * r.val ^ (2 - (n : ℤ)) = 1 := by
    rw [← zpow_add₀ r.property.ne']
    have hexp : ((n : ℤ) - 2) + (2 - (n : ℤ)) = 0 := by omega
    rw [hexp, zpow_zero]
  rw [hpower, ENNReal.ofReal_one, one_mul]

/-- Monotonicity supplies actual finite energy on every fixed rescaled ball
whose corresponding source radius lies below the compactly contained outer
radius. -/
theorem IsLocallyEnergyMinimizing.rescaled_ball_energy_bound {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Domain n) (r₀ ρ R : PositiveRadius)
    (hball : Metric.closedBall a r₀.val ⊆ Ω.val) (hsmall : ρ.val * R.val ≤ r₀.val) :
    dirichletEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i)
        (Metric.ball (0 : Domain n) R.val) ≠ ⊤ ∧
      (dirichletEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i)
        (Metric.ball (0 : Domain n) R.val)).toReal ≤
          R.val ^ ((n : ℤ) - 2) * (normalizedEnergy Du a r₀).toReal := by
  have heq : normalizedEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i) 0 R =
      normalizedEnergy Du a ⟨ρ.val * R.val, mul_pos ρ.property R.property⟩ := by
    simpa only [smul_zero, add_zero] using normalizedEnergy_affine_pullback a 0 ρ R Du
  have hmono : normalizedEnergy Du a ⟨ρ.val * R.val, mul_pos ρ.property R.property⟩ ≤
      normalizedEnergy Du a r₀ :=
    (hmin.normalizedEnergy_monotoneOn hn hu hN r₀.property hball) hsmall (show r₀.val ≤ r₀.val from le_rfl) hsmall
  have hle : dirichletEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i)
      (Metric.ball (0 : Domain n) R.val) ≤
      ENNReal.ofReal (R.val ^ ((n : ℤ) - 2)) * normalizedEnergy Du a r₀ := by
    rw [dirichletEnergy_ball_eq_mul_normalizedEnergy, heq]
    exact mul_le_mul_right hmono _
  have hfinite : ENNReal.ofReal (R.val ^ ((n : ℤ) - 2)) * normalizedEnergy Du a r₀ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hu.normalizedEnergy_ne_top_ball hball)
  refine ⟨ne_top_of_le_ne_top hfinite hle, ?_⟩
  have hreal := ENNReal.toReal_mono hfinite hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (zpow_pos R.property _))] at hreal
  exact hreal

/-- Every prescribed positive scale sequence tending to zero eventually has
one uniform finite energy bound on each fixed rescaled ball. -/
theorem IsLocallyEnergyMinimizing.rescaled_sequence_eventually_energy_bound {n q : ℕ}
    (hn : 2 ≤ n) {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Domain n) (r₀ R : PositiveRadius)
    (hball : Metric.closedBall a r₀.val ⊆ Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ k in atTop,
      dirichletEnergy (fun z i => (ρ k).val • Du (a + (ρ k).val • z) i)
          (Metric.ball (0 : Domain n) R.val) ≠ ⊤ ∧
        (dirichletEnergy (fun z i => (ρ k).val • Du (a + (ρ k).val • z) i)
          (Metric.ball (0 : Domain n) R.val)).toReal ≤
            R.val ^ ((n : ℤ) - 2) * (normalizedEnergy Du a r₀).toReal := by
  have hscale : Tendsto (fun k => (ρ k).val * R.val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hρ.mul_const R.val
  filter_upwards [hscale.eventually (gt_mem_nhds r₀.property)] with k hk
  exact hmin.rescaled_ball_energy_bound hn hu hN a r₀ (ρ k) R hball hk.le

end HarmonicMaps
