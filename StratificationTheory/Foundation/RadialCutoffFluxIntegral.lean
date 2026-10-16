module

public import StratificationTheory.Foundation.RadialScalarCutoff
public import StratificationTheory.Foundation.AngularL2Membership
public import HarmonicMaps.Analysis.BallPolarIntegral
public import HarmonicMaps.Analysis.RadialCutoffDerivative
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual spatial cutoff pairings as native radial flux integrals

The derivative of the original smooth scalar cutoff is supported in its
positive transition band. Polar integration identifies its original spatial
pairing with the original map's native angular flux, without imposing weak
gluing or boundary membership as a premise.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff
namespace StratificationTheory

/-- An actual cutoff derivative paired with the original integrable map is
the interval integral of that same map's native scalar radial flux. The raw
flux identity is only required almost everywhere on the transition interval. -/
theorem integral_radial_cutoff_eq_flux {n q : ℕ} (hn : 0 < n)
    (Ω : OpenDomain n) (c : Domain n) (u : Domain n → Ambient q)
    (hu : IntegrableOn u Ω.val) (ψ : Domain n → ℝ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (i : Fin n) (j : Fin q)
    (t δ : PositiveRadius)
    (hband : {x : Domain n | t.val ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ t.val + δ.val} ⊆ Ω.val)
    (J : ℝ → ℝ)
    (hJ : ∀ᵐ s : ℝ ∂volume, s ∈ Icc t.val (t.val + δ.val) →
      J s = s ^ (n - 1) * ∫ θ : sphere (0 : Domain n) 1,
        (u (c + s • θ.val)) j * ψ (c + s • θ.val) * θ.val i
          ∂Measure.euclideanHausdorffMeasure (n - 1)) :
    (∫ x in Ω.val, (ψ x * coordinateDerivative
      (fun y : Domain n => radialCutoffProfile t δ ‖y - c‖)
        (radialCutoffScalar_contDiff t δ c) i x) * (u x) j) =
      ∫ s in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) s * J s := by
  let χ : Domain n → ℝ := fun x => radialCutoffProfile t δ ‖x - c‖
  have hχ : ContDiff ℝ ∞ χ := radialCutoffScalar_contDiff t δ c
  let g : Domain n → ℝ := fun x => (ψ x * coordinateDerivative χ hχ i x) * (u x) j
  have hweight : MemLp (fun x => ψ x * coordinateDerivative χ hχ i x) ∞
      (volume.restrict Ω.val) :=
    (hψ.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
      hcψ.mul_right _
  have hg : IntegrableOn g Ω.val := by
    have hi := ((EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp hu).smul_of_top_right hweight
    exact hi
  let F : Domain n → ℝ := Ω.val.indicator g
  have hF : Integrable F volume :=
    (integrable_indicator_iff Ω.property.measurableSet).mpr hg
  have hpolar := integral_eq_polar hn hF c
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at hpolar
  have hpolarEq :
      (fun s : ℝ => s ^ (n - 1) * ∫ θ : sphere (0 : Domain n) 1,
        F (c + s • θ.val) ∂Measure.euclideanHausdorffMeasure (n - 1)) =ᵐ[
          volume.restrict (Ioi (0 : ℝ))]
      (Icc t.val (t.val + δ.val)).indicator
        (fun s => deriv (radialCutoffProfile t δ) s * J s) := by
    filter_upwards [ae_restrict_of_ae hJ, ae_restrict_mem measurableSet_Ioi] with s hs hspos
    have hnorm (θ : sphere (0 : Domain n) 1) : ‖c + s • θ.val - c‖ = s := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hspos.le,
        mem_sphere_zero_iff_norm.mp θ.property, mul_one]
    have hdir (θ : sphere (0 : Domain n) 1) :
        s⁻¹ * (c + s • θ.val - c) i = θ.val i := by
      rw [add_sub_cancel_left]
      change s⁻¹ * (s * θ.val i) = θ.val i
      rw [← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]
    by_cases hsband : s ∈ Icc t.val (t.val + δ.val)
    · rw [indicator_of_mem hsband, hs hsband]
      have hpoint (θ : sphere (0 : Domain n) 1) :
          F (c + s • θ.val) = deriv (radialCutoffProfile t δ) s *
            ((u (c + s • θ.val)) j * ψ (c + s • θ.val) * θ.val i) := by
        have hxΩ : c + s • θ.val ∈ Ω.val := hband (by simpa only [mem_setOf_eq, hnorm, mem_Icc] using hsband)
        rw [show F (c + s • θ.val) = g (c + s • θ.val) from indicator_of_mem hxΩ g]
        dsimp only [g, χ]
        rw [radialCutoffScalar_coordinateDerivative, hnorm, hdir]
        ring
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    · rw [indicator_of_notMem hsband]
      have hd : deriv (radialCutoffProfile t δ) s = 0 :=
        radialCutoffProfile_deriv_eq_zero t δ hsband
      have hpoint (θ : sphere (0 : Domain n) 1) : F (c + s • θ.val) = 0 := by
        by_cases hxΩ : c + s • θ.val ∈ Ω.val
        · rw [show F (c + s • θ.val) = g (c + s • θ.val) from indicator_of_mem hxΩ g]
          dsimp only [g, χ]
          rw [radialCutoffScalar_coordinateDerivative, hnorm, hd, zero_mul, mul_zero, zero_mul]
        · exact indicator_of_notMem hxΩ g
      simp only [hpoint, integral_zero, mul_zero]
  calc
    _ = ∫ x, F x := (integral_indicator Ω.property.measurableSet).symm
    _ = _ := hpolar
    _ = ∫ s in Ioi (0 : ℝ), (Icc t.val (t.val + δ.val)).indicator
        (fun s => deriv (radialCutoffProfile t δ) s * J s) s := integral_congr_ae hpolarEq
    _ = ∫ s in Icc t.val (t.val + δ.val), deriv (radialCutoffProfile t δ) s * J s := by
      have hsub : Icc t.val (t.val + δ.val) ⊆ Ioi (0 : ℝ) :=
        fun s hs => t.property.trans_le hs.1
      rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub]
    _ = _ := by
      rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right δ.property.le),
        integral_Icc_eq_integral_Ioc]

end StratificationTheory
