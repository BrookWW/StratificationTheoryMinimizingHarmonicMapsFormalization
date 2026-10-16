module

public import StratificationTheory.TangentMaps.PrescribedTangentExtraction
public import StratificationTheory.Foundation.BlowupDensityComparison
public import StratificationTheory.Foundation.HomogeneousSingularRays
public import StratificationTheory.Frozen.RegularDensity
public import Mathlib.Analysis.SpecificLimits.Basic

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- The singular set of a three-dimensional locally minimizing map has no
accumulation point inside the actual open source domain. -/
theorem singularSet_no_accumulation_three {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 3)
    (u : Domain 3 → Ambient q) (Du : Domain 3 → Gradient 3 q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) (a : Ω.val) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : Ω.val, x ∈ singularSet Ω u →
      dist x.val a.val < r → x = a := by
  classical
  by_contra hNot
  push Not at hNot
  have hSelect (k : ℕ) : ∃ x : Ω.val, x ∈ singularSet Ω u ∧
      dist x.val a.val < 1 / ((k : ℝ) + 1) ∧ x ≠ a :=
    hNot (1 / ((k : ℝ) + 1)) (by positivity)
  choose x hxSing hxDist hxNe using hSelect
  have hDistPos (k : ℕ) : 0 < dist (x k).val a.val :=
    dist_pos.mpr (fun h => hxNe k (Subtype.ext h))
  let ρ : ℕ → PositiveRadius := fun k => ⟨dist (x k).val a.val, hDistPos k⟩
  have hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => dist_nonneg) (fun k => (hxDist k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let z : ℕ → Domain 3 := fun k => (ρ k).val⁻¹ • ((x k).val - a.val)
  have hzNorm (k : ℕ) : ‖z k‖ = 1 := by
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ρ k).property),
      ← dist_eq_norm, inv_mul_cancel₀ (ρ k).property.ne']
  obtain ⟨κ, φ, Dφ, hκ, hφ, hTφ, hMinφ, hStrong, _hEnergy, hHom, _hTangent⟩ :=
    exists_tangent_along_prescribed_scales (by norm_num : 2 ≤ 3) N Ω u Du hu hTarget hMinimizer a ρ hρ
  have hzSphere (k : ℕ) : z (κ k) ∈ sphere (0 : Domain 3) 1 := by
    simpa only [mem_sphere, dist_zero_right] using hzNorm (κ k)
  obtain ⟨b, hbSphere, η, hη, hηConv⟩ :=
    (isCompact_sphere (0 : Domain 3) 1).isSeqCompact hzSphere
  have hbNonzero : b ≠ 0 := by
    have hbNorm : ‖b‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hbSphere
    intro hb
    simp only [hb, norm_zero] at hbNorm
    norm_num at hbNorm
  let scales : ℕ → PositiveRadius := fun k => ρ (κ (η k))
  have hScales : Tendsto (fun k => (scales k).val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [scales, Function.comp_def] using
      (hρ.comp hκ.tendsto_atTop).comp hη.tendsto_atTop
  have hStrongSub : ∀ K : Set (Domain 3), IsCompact K →
      Tendsto (fun k => eLpNorm ((fun w => u (a.val + (scales k).val • w)) - φ)
        2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin 3, Tendsto (fun k => eLpNorm
        (fun w => (scales k).val • Du (a.val + (scales k).val • w) i - Dφ w i)
          2 (volume.restrict K)) atTop (𝓝 0) := by
    intro K hK
    exact ⟨by simpa only [scales, Function.comp_def] using (hStrong K hK).1.comp hη.tendsto_atTop,
      fun i => by simpa only [scales, Function.comp_def] using ((hStrong K hK).2 i).comp hη.tendsto_atTop⟩
  have hPosition (k : ℕ) : (x (κ (η k))).val =
      a.val + (scales k).val • z (κ (η k)) := by
    dsimp only [z, scales]
    rw [smul_smul, mul_inv_cancel₀ (ρ (κ (η k))).property.ne', one_smul]
    abel
  have hUpper := (blowup_density_joint_upper_bound (by norm_num : 2 ≤ 3)
    N Ω u Du hu hTarget hMinimizer a scales hScales φ Dφ hφ hTφ hMinφ hStrongSub
    (fun k => z (κ (η k))) (fun k => sphere_subset_closedBall (hzSphere (η k)))
    b hηConv (fun k => x (κ (η k))) hPosition).1
  have hbReg := isRegularPoint_of_ae_homogeneous_minimizer_three hMinφ hφ hTφ hHom b hbNonzero
  obtain ⟨ε, hε, hReg⟩ := regularPoint_density_characterization (by norm_num : 2 ≤ 3) N
  have hbDensity : density (by norm_num : 2 ≤ 3) hMinφ hφ hTφ ⟨b, mem_univ b⟩ = 0 :=
    (hReg ⟨univ, isOpen_univ⟩ φ Dφ hMinφ hφ hTφ ⟨b, mem_univ b⟩).1.mp hbReg
  obtain ⟨k, hk⟩ := (hUpper (ε / 2) (half_pos hε)).exists
  have hLower := (hReg Ω u Du hMinimizer hu hTarget (x (κ (η k)))).2 (hxSing _)
  rw [hbDensity] at hk
  linarith

end StratificationTheory
