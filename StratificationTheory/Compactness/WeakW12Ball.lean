module

public import StratificationTheory.Compactness.TargetL2Bounds
public import StratificationTheory.Compactness.RellichBall
public import StratificationTheory.Compactness.GradientWeakSubsequence
public import StratificationTheory.Compactness.WeakGradientClosure
public import StratificationTheory.Compactness.ClosedTargetLimit
public import HarmonicMaps.SobolevRestriction

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- On an interior ball, compact-target Sobolev maps with uniformly bounded
HS energy admit one strong-map and weak-gradient subsequence. The limit has
the original Sobolev and almost-everywhere target semantics. -/
theorem exists_weak_W12_subsequence_ball {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (a : Domain n) {r R : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12 (ballDomain a R) (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N (ballDomain a R) (u k))
    (C : ℝ≥0) (hEnergy : ∀ k, dirichletEnergy (Du k) (Metric.ball a R) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12 (ballDomain a r) v Dv ∧ TakesValuesIn N (ballDomain a r) v ∧
      dirichletEnergy Dv (Metric.ball a r) ≤ C ∧
      Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict (Metric.ball a r)))
        atTop (𝓝 0) ∧
      ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict (Metric.ball a r))),
        Tendsto (fun k => ∫ x in Metric.ball a r, inner ℝ (Du (κ k) x i) (w x))
          atTop (𝓝 (∫ x in Metric.ball a r, inner ℝ (Dv x i) (w x))) := by
  obtain ⟨B, hB⟩ := compact_target_uniform_L2_ball_bound N
  let Cmap : ℝ≥0 := ⟨(B : ℝ) ^ 2 * volume.real (Metric.ball a R),
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg⟩
  obtain ⟨κ₀, v, hκ₀, hv, hmap⟩ := memW12_exists_strong_L2_subsequence_ball a hR hrR u Du hu Cmap C
    (fun k => hB a R (u k) (hu k).2.1 (hTarget k)) hEnergy
  have huInner (k : ℕ) : MemW12 (ballDomain a r) (u (κ₀ k)) (Du (κ₀ k)) :=
    (hu (κ₀ k)).to_memW12Loc.memW12_ball (Metric.closedBall_subset_ball hrR)
  have henergyInner (k : ℕ) : dirichletEnergy (Du (κ₀ k)) (Metric.ball a r) ≤ C := by
    apply le_trans _ (hEnergy (κ₀ k))
    exact lintegral_mono_set (Metric.ball_subset_ball hrR.le)
  obtain ⟨κ₁, Dv, hκ₁, hDv, hEv, hweak⟩ :=
    exists_weakly_convergent_gradient_field_ball a r (fun k => Du (κ₀ k))
      (fun k i => (huInner k).2.2 i) C henergyInner
  have hmap' : Tendsto (fun k => eLpNorm (u (κ₀ (κ₁ k)) - v) 2
      (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := hmap.comp hκ₁.tendsto_atTop
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hvW : MemW12 (ballDomain a r) v Dv := memW12_of_strong_map_weak_gradient_limit
    (fun k => huInner (κ₁ k)) hv hDv hmap' hweak
  have hvN : TakesValuesIn N (ballDomain a r) v := takesValuesIn_of_L2_limit N (ballDomain a r)
    (fun k => (huInner (κ₁ k)).2.1) hv
    (fun k => ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hrR.le)
      (hTarget (κ₀ (κ₁ k)))) hmap'
  exact ⟨κ₀ ∘ κ₁, v, Dv, hκ₀.comp hκ₁, hvW, hvN, hEv, hmap', hweak⟩

end StratificationTheory.Compactness
