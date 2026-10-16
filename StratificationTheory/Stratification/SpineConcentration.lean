module

public import StratificationTheory.TangentMaps.PrescribedTangentExtraction
public import StratificationTheory.Foundation.BlowupDensityComparison
public import StratificationTheory.Frozen.SpineCharacterization
public import StratificationTheory.Frozen.SingularSet
public import StratificationTheory.TangentMaps.CenteredConstantEnergy
public import StratificationTheory.Stratification.PlaneExtension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- At a singular point where every actual raw tangent has spine rank at
most j, one positive epsilon controls both radius and density tolerance. -/
theorem exists_spine_concentration_at_stratum_point {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (_hSingular : a ∈ singularSet Ω u) (j : ℕ) (hj : j ≤ n)
    (hRank : ∀ (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      IsTangentAt u Du a.val φ Dφ →
      ∀ (hMinφ : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ)
        (hφ : MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ)
        (hTφ : TakesValuesIn N ⟨univ, isOpen_univ⟩ φ)
        (hHom : ∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ),
        Module.finrank ℝ (spine hn hMinφ hφ hTφ hHom) ≤ j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : PositiveRadius, ρ.val ≤ ε →
      closedBall a.val ρ.val ⊆ Ω.val →
      ∃ L : Subspace ℝ (Domain n), Module.finrank ℝ L = j ∧
        ∀ x : Ω.val, x.val ∈ ball a.val ρ.val →
          density hn hMinimizer hu hTarget a - ε ≤ density hn hMinimizer hu hTarget x →
          infDist (ρ.val⁻¹ • (x.val - a.val)) (L : Set (Domain n)) < δ
 := by
  classical
  by_contra hNo
  push Not at hNo
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεPos (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεZero : Tendsto ε atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hFailure (k : ℕ) : ∃ ρ : PositiveRadius, ρ.val ≤ ε k ∧
      closedBall a.val ρ.val ⊆ Ω.val ∧
      ∀ L : Subspace ℝ (Domain n), Module.finrank ℝ L = j →
        ∃ x : Ω.val, x.val ∈ ball a.val ρ.val ∧
          density hn hMinimizer hu hTarget a - ε k ≤ density hn hMinimizer hu hTarget x ∧
          δ ≤ infDist (ρ.val⁻¹ • (x.val - a.val)) (L : Set (Domain n)) :=
    hNo (ε k) (hεPos k)
  choose ρ hρSmall _hρClosed hBad using hFailure
  have hρZero : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεZero
      (fun k => (ρ k).property.le) hρSmall
  obtain ⟨κ, φ, Dφ, hκ, hφ, hTφ, hMinφ, hStrong, hEnergy, hHom, hTangent⟩ :=
    exists_tangent_along_prescribed_scales hn N Ω u Du hu hTarget hMinimizer a ρ hρZero
  let S := spine hn hMinφ hφ hTφ hHom
  have hSrank : Module.finrank ℝ S ≤ j := hRank φ Dφ hTangent hMinφ hφ hTφ hHom
  obtain ⟨L, hSL, hLrank⟩ := exists_plane_containing_subspace S hSrank hj
  choose x hxBall hxDensity hxFar using fun k => hBad (κ k) L hLrank
  let z : ℕ → Domain n := fun k => (ρ (κ k)).val⁻¹ • ((x k).val - a.val)
  have hzNorm (k : ℕ) : ‖z k‖ < 1 := by
    have hxNorm : ‖(x k).val - a.val‖ < (ρ (κ k)).val := by
      simpa only [mem_ball, dist_eq_norm] using hxBall k
    have hh := mul_lt_mul_of_pos_left hxNorm (inv_pos.mpr (ρ (κ k)).property)
    simpa only [z, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ρ (κ k)).property),
      inv_mul_cancel₀ (ρ (κ k)).property.ne'] using hh
  have hzClosed (k : ℕ) : z k ∈ closedBall (0 : Domain n) 1 := by
    simpa only [mem_closedBall, dist_zero_right] using (hzNorm k).le
  obtain ⟨b, _hb, τ, hτ, hzConv⟩ := (isCompact_closedBall (0 : Domain n) 1).tendsto_subseq hzClosed
  have hρSub : Tendsto (fun k => (ρ (κ (τ k))).val) atTop (𝓝 (0 : ℝ)) :=
    hρZero.comp (hκ.comp hτ).tendsto_atTop
  have hStrongSub : ∀ K : Set (Domain n), IsCompact K →
      Tendsto (fun k => eLpNorm ((fun w => u (a.val + (ρ (κ (τ k))).val • w)) - φ)
        2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun w => (ρ (κ (τ k))).val • Du (a.val + (ρ (κ (τ k))).val • w) i - Dφ w i)
          2 (volume.restrict K)) atTop (𝓝 0) := by
    intro K hK
    exact ⟨((hStrong K hK).1).comp hτ.tendsto_atTop,
      fun i => ((hStrong K hK).2 i).comp hτ.tendsto_atTop⟩
  have hxAffine (k : ℕ) : (x (τ k)).val = a.val + (ρ (κ (τ k))).val • z (τ k) := by
    simp only [z, smul_smul, mul_inv_cancel₀ (ρ (κ (τ k))).property.ne',
      one_smul, add_sub_cancel]
  obtain ⟨hUpper, _hLimsup⟩ := blowup_density_joint_upper_bound hn N Ω u Du hu hTarget hMinimizer a
    (fun k => ρ (κ (τ k))) hρSub φ Dφ hφ hTφ hMinφ hStrongSub
    (fun k => z (τ k)) (fun k => hzClosed (τ k)) b hzConv (fun k => x (τ k)) hxAffine
  have hOrigin := TangentMaps.density_origin_eq_constant hn hMinφ hφ hTφ
    (density hn hMinimizer hu hTarget a) hEnergy
  have hDensityLe : density hn hMinimizer hu hTarget a ≤
      density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ := by
    by_contra hnot
    have hGap : 0 < density hn hMinimizer hu hTarget a - density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hSmall := (hεZero.comp (hκ.comp hτ).tendsto_atTop).eventually (gt_mem_nhds (half_pos hGap))
    have hUp := hUpper ((density hn hMinimizer hu hTarget a -
      density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩) / 2) (half_pos hGap)
    obtain ⟨k, hkSmall, hkUp⟩ := (hSmall.and hUp).exists
    have hkLow := hxDensity (τ k)
    dsimp only [Function.comp_def] at hkSmall
    linarith only [hkSmall, hkUp, hkLow]
  have hSpine := spine_characterization hn hMinφ hφ hTφ hHom
  have hDensityEq : density hn hMinφ hφ hTφ ⟨b, mem_univ b⟩ =
      density hn hMinφ hφ hTφ ⟨0, mem_univ 0⟩ := by
    apply le_antisymm (hSpine.2.1 b)
    rw [hOrigin]
    exact hDensityLe
  have hbS : b ∈ S := (hSpine.1 b).mpr hDensityEq
  have hbL : b ∈ L := hSL hbS
  have hFar : δ ≤ infDist b (L : Set (Domain n)) :=
    ge_of_tendsto ((continuous_infDist_pt (L : Set (Domain n))).tendsto b |>.comp hzConv)
      (Eventually.of_forall fun k => hxFar (τ k))
  rw [infDist_zero_of_mem hbL] at hFar
  exact (not_le_of_gt hδ) hFar

end StratificationTheory
