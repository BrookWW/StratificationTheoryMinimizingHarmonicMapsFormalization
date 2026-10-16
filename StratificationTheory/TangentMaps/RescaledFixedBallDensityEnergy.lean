module

public import StratificationTheory.TangentMaps.RescaledFixedBallStrongCompactness
public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.Compactness.StrongGradientEnergy

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory

/-- One actual fixed-ball blow-up limit retains its full strong compactness
data and has the original point density as its normalized energy at every
strictly smaller positive radius. -/
theorem exists_rescaled_fixed_ball_strong_subsequence_with_density_energy {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) (L : PositiveRadius) :
    let U : ℕ → Domain n → Ambient q := fun k x => u (a.val + (ρ k).val • x)
    let D : ℕ → Domain n → Gradient n q := fun k x i => (ρ k).val • Du (a.val + (ρ k).val • x) i
    ∃ (tail : ℕ) (κ : ℕ → ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      (∀ j, tail ≤ j →
        MemW12 (ballDomain (0 : Domain n) L.val) (U j) (D j) ∧
        TakesValuesIn N (ballDomain (0 : Domain n) L.val) (U j) ∧
        IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) (U j) (D j)) ∧
      StrictMono κ ∧ (∀ k, tail ≤ κ k) ∧
      MemW12Loc (ballDomain (0 : Domain n) L.val) v Dv ∧
      TakesValuesIn N (ballDomain (0 : Domain n) L.val) v ∧
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) v Dv ∧
      (∀ K : Set (Domain n), IsCompact K → K ⊆ (ballDomain (0 : Domain n) L.val).val →
        Tendsto (fun k => eLpNorm (U (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (κ k) x i - Dv x i)
          2 (volume.restrict K)) atTop (𝓝 0)) ∧
      ∀ R : PositiveRadius, R.val < L.val →
        (normalizedEnergy Dv (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a := by
  intro U D
  obtain ⟨tail, κ, v, Dv, hActual, hκ, hκTail, hv, hvN, hMinV, hStrong⟩ :=
    exists_rescaled_fixed_ball_strong_subsequence hn N Ω u Du hu hTarget hMinimizer a ρ hρ L
  refine ⟨tail, κ, v, Dv, hActual, hκ, hκTail, hv, hvN, hMinV, hStrong, ?_⟩
  intro R hRL
  have hClosedR : closedBall (0 : Domain n) R.val ⊆ (ballDomain (0 : Domain n) L.val).val :=
    closedBall_subset_ball hRL
  have hUR (k : ℕ) : MemW12 (ballDomain (0 : Domain n) R.val) (U (κ k)) (D (κ k)) :=
    (hActual (κ k) (hκTail k)).1.to_memW12Loc.memW12_ball hClosedR
  have hvR : MemW12 (ballDomain (0 : Domain n) R.val) v Dv := hv.memW12_ball hClosedR
  have hS (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => D (κ k) x i - Dv x i)
      2 (volume.restrict (ball (0 : Domain n) R.val))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((hStrong (closedBall (0 : Domain n) R.val) (isCompact_closedBall _ _) hClosedR).2 i)
      (fun _ => zero_le)
    exact fun _ => eLpNorm_mono_measure _
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  have hEnergy := Compactness.integral_hsNormSq_tendsto_of_strong_columns
    (fun k i => (hUR k).2.2 i) (fun i => hvR.2.2 i) hS
  have hNormalized : Tendsto (fun k => (normalizedEnergy (D (κ k)) (0 : Domain n) R).toReal)
      atTop (𝓝 ((normalizedEnergy Dv (0 : Domain n) R).toReal)) := by
    simpa only [normalizedEnergy_toReal (hUR _).integrable_hsNormSq,
      normalizedEnergy_toReal hvR.integrable_hsNormSq, ballDomain, Subtype.coe_mk] using
      hEnergy.const_mul (R.val ^ ((2 : ℤ) - (n : ℤ)))
  let r : ℕ → PositiveRadius := fun k =>
    ⟨(ρ (κ k)).val * R.val, mul_pos (ρ (κ k)).property R.property⟩
  have hScale : Tendsto (fun k => (ρ (κ k)).val * R.val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul, Function.comp_def] using (hρ.comp hκ.tendsto_atTop).mul_const R.val
  have hRad : Tendsto r atTop atBot := by
    apply tendsto_atBot.2
    intro s
    filter_upwards [hScale.eventually (gt_mem_nhds s.property)] with k hk
    exact hk.le
  have hAffine (k : ℕ) : normalizedEnergy (D (κ k)) (0 : Domain n) R =
      normalizedEnergy Du a.val (r k) := by
    simpa only [smul_zero, add_zero] using normalizedEnergy_affine_pullback a.val 0 (ρ (κ k)) R Du
  have hDensity : Tendsto (fun k => (normalizedEnergy (D (κ k)) (0 : Domain n) R).toReal)
      atTop (𝓝 (density hn hMinimizer hu hTarget a)) := by
    have hOriginal := (normalizedEnergy_tendsto_density_atBot hn hMinimizer hu hTarget a).comp hRad
    simpa only [Function.comp_def, hAffine] using hOriginal
  exact tendsto_nhds_unique hNormalized hDensity

end StratificationTheory
