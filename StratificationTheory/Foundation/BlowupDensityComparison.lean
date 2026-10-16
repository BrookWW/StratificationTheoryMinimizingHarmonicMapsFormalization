module

public import StratificationTheory.TangentMaps.RescaledDomains
public import StratificationTheory.Foundation.DensityJointEnergyBound
public import StratificationTheory.Foundation.NormalizedEnergyOrder
public import StratificationTheory.Compactness.StrongGradientEnergy

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

private theorem density_rescaled_on_fixed_ball {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Domain n) (ρ : PositiveRadius) (L : ℝ)
    (hU : MemW12 (ballDomain (0 : Domain n) L)
      (fun z => u (a + ρ.val • z)) (fun z i => ρ.val • Du (a + ρ.val • z) i))
    (hT : TakesValuesIn N (ballDomain (0 : Domain n) L) (fun z => u (a + ρ.val • z)))
    (hM : IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L)
      (fun z => u (a + ρ.val • z)) (fun z i => ρ.val • Du (a + ρ.val • z) i))
    (z : (ballDomain (0 : Domain n) L).val) (x : Ω.val)
    (hx : x.val = a + ρ.val • z.val) :
    density hn hM hU.to_memW12Loc hT z = density hn hMinimizer hu hTarget x := by
  have hScaled : Tendsto (fun r : PositiveRadius =>
      (normalizedEnergy (fun w i => ρ.val • Du (a + ρ.val • w) i) z.val r).toReal)
      atBot (𝓝 (density hn hMinimizer hu hTarget x)) := by
    have hComp := (normalizedEnergy_tendsto_density_atBot hn hMinimizer hu hTarget x).comp
      (positiveRadius_mul_tendsto_atBot ρ.property)
    have hEq : (fun r : PositiveRadius =>
        (normalizedEnergy (fun w i => ρ.val • Du (a + ρ.val • w) i) z.val r).toReal) =
        (fun r : PositiveRadius =>
          (normalizedEnergy Du x.val ⟨ρ.val * r.val, mul_pos ρ.property r.property⟩).toReal) := by
      funext r
      have hh := normalizedEnergy_affine_pullback a z.val ρ r Du
      rw [← hx] at hh
      exact congrArg ENNReal.toReal hh
    rw [hEq]
    exact hComp
  exact tendsto_nhds_unique (normalizedEnergy_tendsto_density_atBot hn hM hU.to_memW12Loc hT z) hScaled

/-- Genuine strong blow-up data on all compact subsets give the actual
moving-point density comparison with the original unscaled map. Fixed-ball
qualifications, energy convergence and density transport are produced inside. -/
theorem blowup_density_joint_upper_bound {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ)))
    (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hφ : MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ)
    (hTφ : TakesValuesIn N ⟨univ, isOpen_univ⟩ φ)
    (hMinφ : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ)
    (hStrong : ∀ K : Set (Domain n), IsCompact K →
      Tendsto (fun k => eLpNorm ((fun z => u (a.val + (ρ k).val • z)) - φ)
        2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun z => (ρ k).val • Du (a.val + (ρ k).val • z) i - Dφ z i)
          2 (volume.restrict K)) atTop (𝓝 0))
    (z : ℕ → Domain n) (hz : ∀ k, z k ∈ closedBall (0 : Domain n) 1)
    (b : Domain n) (hb : Tendsto z atTop (𝓝 b))
    (x : ℕ → Ω.val) (hx : ∀ k, (x k).val = a.val + (ρ k).val • z k) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      density hn hMinimizer hu hTarget (x k) ≤
        density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ + ε) ∧
    Filter.limsup (fun k => density hn hMinimizer hu hTarget (x k)) atTop ≤
      density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ := by
  let B : OpenDomain n := ballDomain (0 : Domain n) 2
  let U : ℕ → Domain n → Ambient q := fun k z => u (a.val + (ρ k).val • z)
  let D : ℕ → Domain n → Gradient n q := fun k z i => (ρ k).val • Du (a.val + (ρ k).val • z) i
  have hQual := eventually_rescaled_minimizer_on_ball N Ω a.property u Du hu hTarget hMinimizer
    (centers := fun _ : ℕ => a.val) (scales := ρ) tendsto_const_nhds hρ ⟨2, by norm_num⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hQual
  have hData (k : ℕ) : MemW12 B (U (J + k)) (D (J + k)) ∧
      TakesValuesIn N B (U (J + k)) ∧ IsLocallyEnergyMinimizing N B (U (J + k)) (D (J + k)) :=
    hJ (J + k) (by omega)
  have hTail : StrictMono (fun k : ℕ => J + k) := fun _ _ h => Nat.add_lt_add_left h J
  have hφB : MemW12Loc B φ Dφ := hφ.mono (subset_univ _)
  have hTφB : TakesValuesIn N B φ := ae_restrict_of_ae_restrict_of_subset (subset_univ _) hTφ
  have hMinφB : IsLocallyEnergyMinimizing N B φ Dφ := by
    intro c r hr _hClosed v Dv hv hvN hBoundary
    exact hMinφ c r hr (subset_univ _) v Dv hv hvN hBoundary
  have hEnergy (c : Domain n) (r : ℝ) (_hr : 0 < r) (hClosed : closedBall c r ⊆ B.val) :
      Tendsto (fun k => ∫ w in ball c r, hsNormSq (D (J + k) w)) atTop
        (𝓝 (∫ w in ball c r, hsNormSq (Dφ w))) := by
    have hD (k : ℕ) (i : Fin n) : MemLp (fun w => D (J + k) w i) 2 (volume.restrict (ball c r)) :=
      ((hData k).1.to_memW12Loc.memW12_ball hClosed).2.2 i
    have hDφ (i : Fin n) : MemLp (fun w => Dφ w i) 2 (volume.restrict (ball c r)) :=
      (hφB.memW12_ball hClosed).2.2 i
    have hS (i : Fin n) : Tendsto (fun k => eLpNorm (fun w => D (J + k) w i - Dφ w i)
        2 (volume.restrict (ball c r))) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (((hStrong (closedBall c r) (isCompact_closedBall c r)).2 i).comp hTail.tendsto_atTop)
        (fun _ => zero_le)
      exact fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume ball_subset_closedBall)
    exact Compactness.integral_hsNormSq_tendsto_of_strong_columns hD hDφ hS
  have hzB (k : ℕ) : z k ∈ B.val := (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)) (hz k)
  have hbClosed : b ∈ closedBall (0 : Domain n) 1 :=
    isClosed_closedBall.mem_of_tendsto hb (Eventually.of_forall hz)
  let bB : B.val := ⟨b, (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)) hbClosed⟩
  let zB : ℕ → B.val := fun k => ⟨z (J + k), hzB (J + k)⟩
  have hzConv : Tendsto (fun k => (zB k).val) atTop (𝓝 bB.val) := hb.comp hTail.tendsto_atTop
  have hDensityφ : density hn hMinφB hφB hTφB bB = density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ :=
    tendsto_nhds_unique (normalizedEnergy_tendsto_density_atBot hn hMinφB hφB hTφB bB)
      (normalizedEnergy_tendsto_density_atBot hn hMinφ hφ hTφ ⟨b, mem_univ b⟩)
  have hDensityU (k : ℕ) :
      density hn (hData k).2.2 (hData k).1.to_memW12Loc (hData k).2.1 (zB k) =
        density hn hMinimizer hu hTarget (x (J + k)) :=
    density_rescaled_on_fixed_ball hn N Ω u Du hu hTarget hMinimizer a.val (ρ (J + k)) 2
      (hData k).1 (hData k).2.1 (hData k).2.2 (zB k) (x (J + k)) (hx (J + k))
  have hTailUpper := (density_joint_upper_bound_of_ball_energy_convergence hn N B
    (fun k => U (J + k)) (fun k => D (J + k)) φ Dφ
    (fun k => (hData k).1.to_memW12Loc) (fun k => (hData k).2.1) (fun k => (hData k).2.2)
    hφB hTφB hMinφB hEnergy bB zB hzConv).1
  have hUpper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop,
      density hn hMinimizer hu hTarget (x k) ≤ density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ + ε := by
    have hh := hTailUpper ε hε
    simp only [hDensityU, hDensityφ] at hh
    obtain ⟨K, hK⟩ := eventually_atTop.mp hh
    refine eventually_atTop.mpr ⟨J + K, ?_⟩
    intro k hk
    have hJK : J + (k - J) = k := Nat.add_sub_of_le (by omega)
    have hhK := hK (k - J) (by omega)
    rw [hJK] at hhK
    exact hhK
  have hCobounded : atTop.IsCoboundedUnder (· ≤ ·)
      (fun k => density hn hMinimizer hu hTarget (x k)) :=
    isCoboundedUnder_le_of_le atTop (fun k => density_nonneg hn hMinimizer hu hTarget (x k))
  have hBounded : atTop.IsBoundedUnder (· ≤ ·)
      (fun k => density hn hMinimizer hu hTarget (x k)) :=
    isBoundedUnder_of_eventually_le (hUpper 1 zero_lt_one)
  refine ⟨hUpper, (limsup_le_iff' hCobounded hBounded).mpr ?_⟩
  intro t ht
  filter_upwards [hUpper (t - density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩) (sub_pos.mpr ht)] with k hk
  linarith

end StratificationTheory
