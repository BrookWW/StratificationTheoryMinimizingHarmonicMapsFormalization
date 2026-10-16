module

public import StratificationTheory.TangentMaps.TangentRelation
public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.TangentMaps.RescaledNestedBallFamily
public import StratificationTheory.TangentMaps.NestedBallStrongGluing
public import StratificationTheory.Foundation.GlobalMinimizerBallAssembly
public import StratificationTheory.Foundation.RadialHomogeneity

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory.Providers.PrescribedTangentExtraction

/-- Every prescribed positive shrinking scale sequence admits one global
locally minimizing tangent, with one common subsequence on all compact sets,
all-radius source-density energy and degree-zero AE homogeneity. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) :
    ∃ (κ : ℕ → ℕ) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ ∧
      TakesValuesIn N ⟨univ, isOpen_univ⟩ φ ∧
      IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ ∧
      (∀ K : Set (Domain n), IsCompact K →
        Tendsto (fun k => eLpNorm
          ((fun x => u (a.val + (ρ (κ k)).val • x)) - φ) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm
          (fun x => (ρ (κ k)).val • Du (a.val + (ρ (κ k)).val • x) i - Dφ x i)
            2 (volume.restrict K)) atTop (𝓝 0)) ∧
      (∀ R : PositiveRadius,
        (normalizedEnergy Dφ (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a) ∧
      (∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ) ∧
      IsTangentAt u Du a.val φ Dφ := by
  let U : ℕ → Domain n → Ambient q := fun k x => u (a.val + (ρ k).val • x)
  let D : ℕ → Domain n → Gradient n q := fun k x i => (ρ k).val • Du (a.val + (ρ k).val • x) i
  obtain ⟨σ, η, v, Dv, _hZero, hStep, hFamily⟩ :=
    exists_rescaled_nested_ball_family hn N Ω u Du hu hTarget hMinimizer a ρ hρ
  obtain ⟨κ, φ, Dφ, hκ, hMap, hGrad, hConv⟩ :=
    exists_nested_ball_strong_gluing σ η hStep U D v Dv
      (fun j => (hFamily j).1) (fun j => (hFamily j).2.1)
      (fun j => (hFamily j).2.2.2.2.1)
  obtain ⟨hφ, hφN, hφMin⟩ := global_minimizer_of_ae_expanding_ball_family N φ Dφ v Dv
    (fun j => (hFamily j).2.1) (fun j => (hFamily j).2.2.1)
    (fun j => (hFamily j).2.2.2.1) hMap hGrad
  have hEnergy : ∀ R : PositiveRadius,
      (normalizedEnergy Dφ (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a := by
    intro R
    obtain ⟨j, hj⟩ := exists_nat_gt R.val
    have hRK : ball (0 : Domain n) R.val ⊆ closedBall 0 ((j : ℝ) + 1) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    have hD : Dφ =ᵐ[volume.restrict (ball 0 R.val)] Dv j :=
      ae_restrict_of_ae_restrict_of_subset hRK (hGrad j)
    have hEq : normalizedEnergy Dφ (0 : Domain n) R = normalizedEnergy (Dv j) 0 R := by
      unfold normalizedEnergy
      rw [dirichletEnergy_congr_ae hD]
    rw [hEq]
    exact (hFamily j).2.2.2.2.2 R (by linarith)
  have hHom : ∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ := by
    intro l hl
    simpa only [zero_add, sub_zero] using
      hφMin.ae_eq_rescale_of_constant_energy hn hφ hφN (0 : Domain n)
        (density hn hMinimizer hu hTarget a) hEnergy hl
  refine ⟨κ, φ, Dφ, hκ, hφ, hφN, hφMin, (fun K hK => (hConv K hK).2), hEnergy, hHom, ?_⟩
  refine ⟨hφ.2.1, (fun i => hφ.2.2 i), (fun k => ρ (κ k)), ?_, ?_⟩
  · simpa only [Function.comp_def] using hρ.comp hκ.tendsto_atTop
  · intro K hK
    exact hConv K hK

end StratificationTheory.Providers.PrescribedTangentExtraction
