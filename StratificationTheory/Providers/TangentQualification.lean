module

public import StratificationTheory.TangentMaps.PrescribedTangentExtraction
public import StratificationTheory.Foundation.MinimizerAECongruence
public import HarmonicMaps.Analysis.SobolevAECongruence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory.Providers.TangentQualification

private theorem ae_eq_of_eventual_strong_limits {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f : ℕ → α → E} {g h : α → E}
    (hf : ∀ᶠ k in atTop, MemLp (f k) 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hfg : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0))
    (hfh : Tendsto (fun k => eLpNorm (f k - h) 2 μ) atTop (𝓝 0)) : g =ᵐ[μ] h := by
  obtain ⟨m, hm⟩ := eventually_atTop.mp hf
  have hfgTail : Tendsto (fun k => eLpNorm (f (k + m) - g) 2 μ) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hfg.comp (tendsto_add_atTop_nat m)
  have hfhTail : Tendsto (fun k => eLpNorm (f (k + m) - h) 2 μ) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hfh.comp (tendsto_add_atTop_nat m)
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hm (k + m) (by omega)).aestronglyMeasurable) hg.aestronglyMeasurable hfgTail)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hm (k + m) (by omega)).aestronglyMeasurable) hh.aestronglyMeasurable hfhTail)

private theorem ae_eq_of_eq_on_nat_closed_balls {n : ℕ} {E : Type*}
    {f g : Domain n → E}
    (h : ∀ j : ℕ, f =ᵐ[volume.restrict (closedBall 0 ((j : ℝ) + 1))] g) :
    f =ᵐ[volume] g := by
  have hCover : (⋃ j : ℕ, closedBall (0 : Domain n) ((j : ℝ) + 1)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hAll := (ae_eq_restrict_iUnion_iff
    (fun j : ℕ => closedBall (0 : Domain n) ((j : ℝ) + 1)) f g).mpr h
  simpa only [hCover, Measure.restrict_univ] using hAll

/-- Every actual raw strong tangent limit has the original global weak,
target, minimizing, density-energy and homogeneity properties. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hT : IsTangentAt u Du a.val φ Dφ) :
    MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ ∧
      TakesValuesIn N ⟨univ, isOpen_univ⟩ φ ∧
      IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ ∧
      (∀ R : PositiveRadius,
        (normalizedEnergy Dφ (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a) ∧
      ∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ := by
  obtain ⟨hφLp, hDφLp, ρ, hρ, hUser⟩ := hT
  obtain ⟨κ, ψ, Dψ, hκ, hψ, hψN, hψMin, hGoodStrong, hGoodEnergy, _hGoodHom, _hGoodTangent⟩ :=
    exists_tangent_along_prescribed_scales hn N Ω u Du hu hTarget hMinimizer a ρ hρ
  have hMapK (K : Set (Domain n)) (hK : IsCompact K) : φ =ᵐ[volume.restrict K] ψ := by
    have hRaw := hκ.tendsto_atTop.eventually ((hUser K hK).1)
    have hUserMap : Tendsto (fun k => eLpNorm
        ((fun x => u (a.val + (ρ (κ k)).val • x)) - φ) 2 (volume.restrict K)) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using ((hUser K hK).2.1.comp hκ.tendsto_atTop)
    exact ae_eq_of_eventual_strong_limits (hRaw.mono fun _ hk => hk.1)
      (hφLp K hK (subset_univ _)) (hψ.2.1 K hK (subset_univ _))
      hUserMap (hGoodStrong K hK).1
  have hGradK (K : Set (Domain n)) (hK : IsCompact K) : Dφ =ᵐ[volume.restrict K] Dψ := by
    have hRaw := hκ.tendsto_atTop.eventually ((hUser K hK).1)
    have hCols (i : Fin n) : (fun x => Dφ x i) =ᵐ[volume.restrict K] (fun x => Dψ x i) := by
      have hUserCol : Tendsto (fun k => eLpNorm
          (fun x => (ρ (κ k)).val • Du (a.val + (ρ (κ k)).val • x) i - Dφ x i)
            2 (volume.restrict K)) atTop (𝓝 0) := by
        simpa only [Function.comp_def] using ((hUser K hK).2.2 i).comp hκ.tendsto_atTop
      exact ae_eq_of_eventual_strong_limits (hRaw.mono fun _ hk => hk.2 i)
        (hDφLp i K hK (subset_univ _)) (hψ.2.2 i K hK (subset_univ _))
        hUserCol ((hGoodStrong K hK).2 i)
    filter_upwards [ae_all_iff.mpr hCols] with x hx
    exact funext hx
  have hMap : φ =ᵐ[volume] ψ := ae_eq_of_eq_on_nat_closed_balls
    (fun _ => hMapK _ (isCompact_closedBall _ _))
  have hGrad : Dφ =ᵐ[volume] Dψ := ae_eq_of_eq_on_nat_closed_balls
    (fun _ => hGradK _ (isCompact_closedBall _ _))
  have hMapU : ψ =ᵐ[volume.restrict (univ : Set (Domain n))] φ := ae_restrict_of_ae hMap.symm
  have hGradU : Dψ =ᵐ[volume.restrict (univ : Set (Domain n))] Dφ := ae_restrict_of_ae hGrad.symm
  have hW : MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ := hψ.congr_ae hMapU hGradU
  have hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ φ := by
    filter_upwards [hψN, hMapU] with x hxN hx
    rw [← hx]
    exact hxN
  have hMin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ :=
    hψMin.congr_ae hMapU hGradU
  have hEnergy : ∀ R : PositiveRadius,
      (normalizedEnergy Dφ (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a := by
    intro R
    have hGradR : Dφ =ᵐ[volume.restrict (ball 0 R.val)] Dψ := ae_restrict_of_ae hGrad
    have hEq : normalizedEnergy Dφ (0 : Domain n) R = normalizedEnergy Dψ 0 R := by
      unfold normalizedEnergy
      rw [dirichletEnergy_congr_ae hGradR]
    rw [hEq]
    exact hGoodEnergy R
  refine ⟨hW, hN, hMin, hEnergy, ?_⟩
  intro l hl
  simpa only [zero_add, sub_zero] using
    hMin.ae_eq_rescale_of_constant_energy hn hW hN (0 : Domain n)
      (density hn hMinimizer hu hTarget a) hEnergy hl

end StratificationTheory.Providers.TangentQualification
