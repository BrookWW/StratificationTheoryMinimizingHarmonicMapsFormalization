module

public import StratificationTheory.Interpolation.CollarAdmissibility
public import HarmonicMaps.Analysis.SobolevPostcomposition
public import HarmonicMaps.Frozen.TubularProjection
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Projection of actual Sobolev collars

One uniform tubular radius and smooth ambient projection extension give an
admissible target-valued collar from an actual ambient Sobolev map. The map
must have an almost-everywhere tubular range bound and agree almost everywhere
with the original map in an outer collar. The gradient is the weak chain-rule
gradient. These inputs do not supply annular traces or an ambient connector.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal BigOperators

namespace StratificationTheory.Interpolation

/-- A single smooth extension fixes the target and agrees with its actual
nearest projection on a uniform tube, with derivative bound two there. -/
theorem exists_smooth_target_projection {q : ℕ} (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q),
      0 < ρ ∧ ρ ≤ tubularBaseRadius q N ∧ ContDiff ℝ ∞ Q ∧
      (∃ L : ℝ, 0 < L ∧ ∀ z, ‖fderiv ℝ Q z‖ ≤ L) ∧
      (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ z : Ambient q, Metric.infDist z N.carrierSet < ρ →
        ∃ hz : z ∈ tubularTube q N,
          Q z = (tubularProjection q N ⟨z, hz⟩).val ∧
          Q z ∈ N.carrierSet ∧ ‖fderiv ℝ Q z‖ ≤ 2 := by
  obtain ⟨ρ, hρ, hρbase, hsub, _, _, hfix, _, hD, _, _, _, _, Q, hQ, hQeq,
    L, _, hL, _, hQL, _⟩ := tubularProjection_complete q N
  have hnear (z : Ambient q) (hz : Metric.infDist z N.carrierSet < ρ) :
      ∃ ht : z ∈ tubularTube q N,
        Q z = (tubularProjection q N ⟨z, ht⟩).val ∧
        Q z ∈ N.carrierSet ∧ ‖fderiv ℝ Q z‖ ≤ 2 := by
    let V : Set (Ambient q) := {w | Metric.infDist w N.carrierSet < ρ}
    have hV : IsOpen V := isOpen_lt (Metric.continuous_infDist_pt N.carrierSet)
      continuous_const
    have hVsub : V ⊆ tubularTube q N := by
      intro w hw
      change Metric.infDist w N.carrierSet < 2 * tubularBaseRadius q N
      change Metric.infDist w N.carrierSet < ρ at hw
      linarith only [hw, hρ, hρbase]
    have ht := hVsub hz
    have heq := hQeq ⟨z, ht⟩ hz
    have hjet := (tubularProjectionDerivative_characterization q N).1
      ⟨z, ht⟩ V Q hV hz hVsub hQ.contDiffOn (fun w hw => hQeq w hw)
    have hwide : z ∈ {w | Metric.infDist w N.carrierSet < 2 * ρ} := by
      change Metric.infDist z N.carrierSet < 2 * ρ
      linarith only [hz, hρ]
    refine ⟨ht, heq, heq ▸ (tubularProjection q N ⟨z, ht⟩).property, ?_⟩
    rw [hjet]
    exact hD ⟨z, hwide⟩
  refine ⟨ρ, Q, hρ, hρbase, hQ, ⟨L, hL, hQL⟩, ?_, hnear⟩
  intro z hz
  obtain ⟨hp, hP, _⟩ := hfix ⟨z, hz⟩
  have hzsmall : Metric.infDist z N.carrierSet < ρ := by
    rw [Metric.infDist_zero_of_mem hz]
    exact hρ
  have heq := hQeq ⟨z, hsub hp⟩ hzsmall
  rw [hP] at heq
  exact heq

/-- An almost-everywhere derivative bound two gives factor four for the
extended HS energy of the displayed postcomposition columns. -/
theorem dirichletEnergy_postcomposition_le_four {n q : ℕ}
    (Q : Ambient q → Ambient q) (w : Domain n → Ambient q)
    (Dw : Domain n → Gradient n q) (U : Set (Domain n))
    (hD : ∀ᵐ x ∂volume.restrict U, ‖fderiv ℝ Q (w x)‖ ≤ 2) :
    dirichletEnergy (fun x i => fderiv ℝ Q (w x) (Dw x i)) U ≤
      4 * dirichletEnergy Dw U := by
  have hpoint : ∀ᵐ x ∂volume.restrict U,
      hsNormSq (fun i => fderiv ℝ Q (w x) (Dw x i)) ≤ 4 * hsNormSq (Dw x) := by
    filter_upwards [hD] with x hx
    unfold hsNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hnorm : ‖fderiv ℝ Q (w x) (Dw x i)‖ ≤ 2 * ‖Dw x i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    nlinarith only [hnorm, norm_nonneg (fderiv ℝ Q (w x) (Dw x i)), norm_nonneg (Dw x i)]
  unfold dirichletEnergy
  calc
    _ ≤ ∫⁻ x in U, ENNReal.ofReal (4 * hsNormSq (Dw x)) :=
      lintegral_mono_ae (hpoint.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)
    _ = 4 * ∫⁻ x in U, ENNReal.ofReal (hsNormSq (Dw x)) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      norm_num

/-- One projection operator works for every genuine ball Sobolev collar whose
range lies in its uniform tube. It produces target membership, actual weak
columns, graph-norm zero-boundary difference, and the factor-four energy bound. -/
theorem exists_projected_collar_operator_ball {q : ℕ} (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q), 0 < ρ ∧ ContDiff ℝ ∞ Q ∧
      ∀ (n : ℕ) (a : Domain n) (r R : ℝ), 0 < R → 0 ≤ r → r < R →
      ∀ (u w : Domain n → Ambient q) (Du Dw : Domain n → Gradient n q),
        MemW12 (ballDomain a R) u Du → TakesValuesIn N (ballDomain a R) u →
        MemW12 (ballDomain a R) w Dw →
        (∀ᵐ x ∂volume.restrict (Metric.ball a R), Metric.infDist (w x) N.carrierSet < ρ) →
        w =ᵐ[volume.restrict (Metric.ball a R \ Metric.closedBall a r)] u →
        MemW12 (ballDomain a R) (Q ∘ w) (fun x i => fderiv ℝ Q (w x) (Dw x i)) ∧
        TakesValuesIn N (ballDomain a R) (Q ∘ w) ∧
        HasZeroBoundaryDifference (ballDomain a R) u Du (Q ∘ w)
          (fun x i => fderiv ℝ Q (w x) (Dw x i)) ∧
        dirichletEnergy (fun x i => fderiv ℝ Q (w x) (Dw x i)) (Metric.ball a R) ≤
          4 * dirichletEnergy Dw (Metric.ball a R) := by
  obtain ⟨ρ, Q, hρ, _, hQ, ⟨L, _, hQL⟩, hfix, hnear⟩ :=
    exists_smooth_target_projection N
  refine ⟨ρ, Q, hρ, hQ, ?_⟩
  intro n a r R hR hr hrR u w Du Dw hu hNu hw htube hcollar
  have hQw := hw.postcompose hR Q hQ L hQL
  have htarget : TakesValuesIn N (ballDomain a R) (Q ∘ w) := by
    filter_upwards [htube] with x hx
    exact (hnear (w x) hx).choose_spec.2.1
  have hD : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ‖fderiv ℝ Q (w x)‖ ≤ 2 := by
    filter_upwards [htube] with x hx
    exact (hnear (w x) hx).choose_spec.2.2
  have hNcollar : ∀ᵐ x ∂volume.restrict (Metric.ball a R \ Metric.closedBall a r),
      u x ∈ N.carrierSet := ae_restrict_of_ae_restrict_of_subset sdiff_subset hNu
  have hQcollar : u =ᵐ[volume.restrict (Metric.ball a R \ Metric.closedBall a r)] Q ∘ w := by
    filter_upwards [hcollar, hNcollar] with x hx hxN
    dsimp only [Function.comp_apply]
    rw [hx, hfix (u x) hxN]
  exact ⟨hQw, htarget,
    zeroBoundaryDifference_of_ae_eq_outer_collar hR hr hrR hu hQw hQcollar,
    dirichletEnergy_postcomposition_le_four Q w Dw (Metric.ball a R) hD⟩

end StratificationTheory.Interpolation

end
