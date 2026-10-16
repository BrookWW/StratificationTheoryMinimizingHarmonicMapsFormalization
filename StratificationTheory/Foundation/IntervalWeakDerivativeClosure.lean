module

public import HarmonicMaps.Analysis.SobolevL2Closure
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Closure of interval weak derivative identities

Actual L2 convergence on a finite interval preserves integration against
bounded scalar tests. Compact support then identifies the restricted
pairings with the whole-line distributional pairings.
-/

public section
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- On a finite measure space, strong L2 convergence preserves the Bochner
pairing with every fixed essentially bounded scalar test. -/
theorem tendsto_integral_smul_of_L2_convergence {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    {φ : α → ℝ} (hφ : MemLp φ ∞ μ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, φ x • f k x ∂μ) atTop
      (𝓝 (∫ x, φ x • u x ∂μ)) := by
  have hscale : Tendsto (fun k => eLpNorm φ ∞ μ * eLpNorm (f k - u) 2 μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hconv
      (Or.inr hφ.eLpNorm_lt_top.ne)
  have hweighted : Tendsto (fun k => eLpNorm
      ((fun x => φ x • f k x) - (fun x => φ x • u x)) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
      (fun _ => zero_le)
    intro k
    have heq : ((fun x => φ x • f k x) - (fun x => φ x • u x)) = φ • (f k - u) := by
      funext x
      exact (smul_sub (φ x) (f k x) (u x)).symm
    dsimp only
    rw [heq]
    exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2
      ((hf k).sub hu).aestronglyMeasurable φ
  have hmass : Tendsto (fun k => eLpNorm
      ((fun x => φ x • f k x) - (fun x => φ x • u x)) 2 μ *
        μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hweighted
      (Or.inr (by norm_num))
  have hL1 : Tendsto (fun k => eLpNorm
      ((fun x => φ x • f k x) - (fun x => φ x • u x)) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass
      (fun _ => zero_le)
    intro k
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hφ.aestronglyMeasurable.smul (hf k).aestronglyMeasurable).sub
        (hφ.aestronglyMeasurable.smul hu.aestronglyMeasurable))
  exact tendsto_integral_of_L1' _ (hφ.aestronglyMeasurable.smul hu.aestronglyMeasurable)
    (Eventually.of_forall fun k => ((hf k).integrable (by norm_num)).smul_of_top_right hφ) hL1

/-- Limits of actual function and derivative L2 data retain every smooth
compactly supported whole-line weak derivative identity on the interval. -/
theorem interval_weakDerivative_of_L2_convergence {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f g : ℕ → ℝ → E} {u v : ℝ → E}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (Ioo a b)))
    (hg : ∀ k, MemLp (g k) 2 (volume.restrict (Ioo a b)))
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hv : MemLp v 2 (volume.restrict (Ioo a b)))
    (hfconv : Tendsto (fun k => eLpNorm (f k - u) 2
      (volume.restrict (Ioo a b))) atTop (𝓝 0))
    (hgconv : Tendsto (fun k => eLpNorm (g k - v) 2
      (volume.restrict (Ioo a b))) atTop (𝓝 0))
    (hweak : ∀ k (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • f k x) = -(∫ x, φ x • g k x)) :
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • u x) = -(∫ x, φ x • v x) := by
  intro φ hφ hc hs
  let μ : Measure ℝ := volume.restrict (Ioo a b)
  have htest : MemLp φ ∞ μ := hφ.continuous.memLp_top_of_hasCompactSupport hc μ
  have hderiv : MemLp (deriv φ) ∞ μ :=
    (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hc.deriv μ
  have hrestrict (ψ : ℝ → ℝ) (hψ : tsupport ψ ⊆ Ioo a b) (w : ℝ → E) :
      (∫ x in Ioo a b, ψ x • w x) = ∫ x, ψ x • w x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hψ hm)), zero_smul]
  have hdSupport : tsupport (deriv φ) ⊆ Ioo a b := tsupport_deriv_subset.trans hs
  have heq (k : ℕ) : (∫ x in Ioo a b, deriv φ x • f k x) =
      -(∫ x in Ioo a b, φ x • g k x) := by
    rw [hrestrict (deriv φ) hdSupport, hrestrict φ hs]
    exact hweak k φ hφ hc hs
  have hleft := tendsto_integral_smul_of_L2_convergence hderiv hf hu hfconv
  have hright := (tendsto_integral_smul_of_L2_convergence htest hg hv hgconv).neg
  rw [← hrestrict (deriv φ) hdSupport u, ← hrestrict φ hs v]
  exact tendsto_nhds_unique hleft (hright.congr fun k => (heq k).symm)

end StratificationTheory
