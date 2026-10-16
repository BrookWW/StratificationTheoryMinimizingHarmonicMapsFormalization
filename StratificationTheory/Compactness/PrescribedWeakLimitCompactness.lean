module

public import StratificationTheory.Compactness.LocalStrongCompactness
public import StratificationTheory.Compactness.StrongGradientEnergy
public import StratificationTheory.Compactness.SubsequenceConvergence
public import StratificationTheory.Compactness.WeakL2Localization
public import StratificationTheory.Compactness.L2PairingConvergence
public import StratificationTheory.Foundation.MinimizerAECongruence
public import StratificationTheory.Compactness.CofinalCompactExhaustion

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory.Compactness

private theorem identify_strong_local_limit {n q : ℕ} (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (v : Domain n → Ambient q)
    (hu : ∀ k, LocallyMemL2 Ω (u k)) (hv : LocallyMemL2 Ω v)
    (hWeak : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      ∀ w : Lp (Ambient q) 2 (volume.restrict K),
        Tendsto (fun k => ∫ x in K, inner ℝ (u k x) (w x)) atTop
          (𝓝 (∫ x in K, inner ℝ (v x) (w x))))
    (κ : ℕ → ℕ) (hκ : StrictMono κ) (w : Domain n → Ambient q)
    (hw : LocallyMemL2 Ω w)
    (hStrong : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (u (κ k) - w) 2 (volume.restrict K)) atTop (𝓝 0)) :
    w =ᵐ[volume.restrict Ω.val] v := by
  obtain ⟨K, hK, hKΩ, _hMono, hCover, _hCofinal⟩ :=
    exists_cofinal_compact_exhaustion_openDomain Ω
  change ∀ᵐ x ∂volume.restrict Ω.val, w x = v x
  rw [← hCover]
  apply (ae_restrict_iUnion_iff K _).mpr
  intro j
  apply ae_eq_of_weak_L2_limits (hw (K j) (hK j) (hKΩ j)) (hv (K j) (hK j) (hKΩ j))
  · intro z
    exact tendsto_integral_inner_of_L2_convergence
      (fun k => hu (κ k) (K j) (hK j) (hKΩ j)) (hw (K j) (hK j) (hKΩ j))
      (Lp.memLp z) (hStrong (K j) (hK j) (hKΩ j))
  · intro z
    exact (hWeak (K j) (hK j) (hKΩ j) z).comp hκ.tendsto_atTop

/-- A prescribed genuine weak local L2 limit is the minimizing Sobolev limit
of the entire original sequence, with its original gradient and ball energies. -/
theorem exists_prescribed_weak_local_limit_data {n q : ℕ} (hn : 2 ≤ n)
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
    ∃ (Dv : Domain n → Gradient n q) (_hv : MemW12Loc Ω v Dv)
      (_hTv : TakesValuesIn N Ω v) (_hMinV : IsLocallyEnergyMinimizing N Ω v Dv),
      (∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => Du k x i - Dv x i)
          2 (volume.restrict K)) atTop (𝓝 0)) ∧
      ∀ (c : Domain n) (r : ℝ), 0 < r → closedBall c r ⊆ Ω.val →
        Tendsto (fun k => ∫ x in ball c r, hsNormSq (Du k x)) atTop
          (𝓝 (∫ x in ball c r, hsNormSq (Dv x))) := by
  obtain ⟨κ₀, w₀, Dv, hκ₀, hw₀, hTw₀, hMinw₀, hS₀⟩ :=
    strongCompactness_of_local_sobolev hn N Ω u Du hu hTarget hMinimizer hEnergy
  have hAE₀ : w₀ =ᵐ[volume.restrict Ω.val] v :=
    identify_strong_local_limit Ω u v (fun k => (hu k).2.1) hvL2 hWeakMap
      κ₀ hκ₀ w₀ hw₀.2.1 (fun K hK hKΩ => (hS₀ K hK hKΩ).1)
  have hv : MemW12Loc Ω v Dv := hw₀.congr_ae hAE₀ (EventuallyEq.refl _ _)
  have hTv : TakesValuesIn N Ω v := by
    filter_upwards [hTw₀, hAE₀] with x hx hEq
    rw [← hEq]
    exact hx
  have hMinV : IsLocallyEnergyMinimizing N Ω v Dv :=
    hMinw₀.congr_ae hAE₀ (EventuallyEq.refl _ _)
  have hFurther (κ : ℕ → ℕ) (hκ : StrictMono κ) :
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
          Tendsto (fun k => eLpNorm (u (κ (σ k)) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
          ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => Du (κ (σ k)) x i - Dv x i)
            2 (volume.restrict K)) atTop (𝓝 0) := by
    have hEnergyκ : ∀ (a : Domain n) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
        ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du (κ k)) (ball a r) ≤ C := by
      intro a r hr hclosed
      obtain ⟨C, hC⟩ := hEnergy a r hr hclosed
      exact ⟨C, fun k => hC (κ k)⟩
    obtain ⟨σ, w, Dw, hσ, hw, hTw, hMinW, hS⟩ :=
      strongCompactness_of_local_sobolev hn N Ω (fun k => u (κ k)) (fun k => Du (κ k))
        (fun k => hu (κ k)) (fun k => hTarget (κ k)) (fun k => hMinimizer (κ k)) hEnergyκ
    have hAE : w =ᵐ[volume.restrict Ω.val] v :=
      identify_strong_local_limit Ω u v (fun k => (hu k).2.1) hvL2 hWeakMap
        (κ ∘ σ) (hκ.comp hσ) w hw.2.1 (fun K hK hKΩ => (hS K hK hKΩ).1)
    have hDAE : Dw =ᵐ[volume.restrict Ω.val] Dv := hw.1.ae_eq_of_ae_eq_map hv.1 hAE
    refine ⟨σ, hσ, ?_⟩
    intro K hK hKΩ
    have hMapK := ae_restrict_of_ae_restrict_of_subset hKΩ hAE
    have hGradK := ae_restrict_of_ae_restrict_of_subset hKΩ hDAE
    refine ⟨?_, ?_⟩
    · apply ((hS K hK hKΩ).1).congr'
      exact Eventually.of_forall fun k => eLpNorm_congr_ae
        (hMapK.mono fun x hx => congrArg (fun z => u (κ (σ k)) x - z) hx)
    · intro i
      apply ((hS K hK hKΩ).2 i).congr'
      exact Eventually.of_forall fun k => eLpNorm_congr_ae
        (hGradK.mono fun x hx => congrArg (fun D : Gradient n q => Du (κ (σ k)) x i - D i) hx)
  have hWhole : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => Du k x i - Dv x i)
        2 (volume.restrict K)) atTop (𝓝 0) := by
    intro K hK hKΩ
    constructor
    · apply tendsto_of_strict_subsequence
      intro κ hκ
      obtain ⟨σ, hσ, hS⟩ := hFurther κ hκ
      exact ⟨σ, hσ, (hS K hK hKΩ).1⟩
    · intro i
      apply tendsto_of_strict_subsequence
      intro κ hκ
      obtain ⟨σ, hσ, hS⟩ := hFurther κ hκ
      exact ⟨σ, hσ, (hS K hK hKΩ).2 i⟩
  refine ⟨Dv, hv, hTv, hMinV, hWhole, ?_⟩
  intro c r _hr hclosed
  have hD (k : ℕ) (i : Fin n) : MemLp (fun x => Du k x i) 2 (volume.restrict (ball c r)) :=
    ((hu k).memW12_ball hclosed).2.2 i
  have hDv (i : Fin n) : MemLp (fun x => Dv x i) 2 (volume.restrict (ball c r)) :=
    (hv.memW12_ball hclosed).2.2 i
  have hStrong (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => Du k x i - Dv x i)
      2 (volume.restrict (ball c r))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((hWhole (closedBall c r) (isCompact_closedBall c r) hclosed).2 i) (fun _ => zero_le)
    exact fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume ball_subset_closedBall)
  exact integral_hsNormSq_tendsto_of_strong_columns hD hDv hStrong

end StratificationTheory.Compactness
