module

public import StratificationTheory.Foundation.SpherePairAnnularBounds
import StratificationTheory.Foundation.SphereSurfaceIntegral
import HarmonicMaps.SobolevRestriction

public section

open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory.Compactness

/-- One native Sobolev sphere retains any property fixed before selection
that holds at almost every candidate radius, together with the two annular
mean estimates for the original gradients and squared map difference. -/
theorem exists_sphere_pair_annular_bounds_with_property {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    (huN : TakesValuesIn N Ω u) (hvN : TakesValuesIn N Ω v)
    {a : Domain n} {s R : ℝ} (hball : closedBall a R ⊆ Ω.val)
    (hs : 0 < s) (hsR : s < R) (P : ℝ → Prop)
    (hP : ∀ᵐ r ∂volume.restrict (Ioo s R), P r) :
    ∃ r ∈ Ioo s R, P r ∧
      ∃ huR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)),
      ∃ hvR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)),
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)) ∧
        Integrable (fun θ : sphere (0 : Domain n) 1 =>
          hsNormSq (fun i => (sphereGradient hn (fun θ => u (a + r • θ.val)) huR i) θ) +
          hsNormSq (fun i => (sphereGradient hn (fun θ => v (a + r • θ.val)) hvR i) θ))
            (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        Integrable (fun θ : sphere (0 : Domain n) 1 => ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2)
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        r ^ ((n : ℤ) - 3) * (∫ θ : sphere (0 : Domain n) 1,
          hsNormSq (fun i => (sphereGradient hn (fun θ => u (a + r • θ.val)) huR i) θ) +
          hsNormSq (fun i => (sphereGradient hn (fun θ => v (a + r • θ.val)) hvR i) θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          2 * (∫ x in ball a R \ ball a s, hsNormSq (Du x) + hsNormSq (Dv x)) / (R - s) ∧
        r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1,
          ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          2 * (∫ x in ball a R \ ball a s, ‖u x - v x‖ ^ 2) / (R - s) := by
  let Q : ℝ → Prop := fun r => P r ∧
    ∃ huR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)),
      ∃ hvR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)),
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)) ∧
        Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
          (fun i => (sphereGradient hn (fun θ => u (a + r • θ.val)) huR i) θ))
            (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
          (fun i => (sphereGradient hn (fun θ => v (a + r • θ.val)) hvR i) θ))
            (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        Integrable (fun x => hsNormSq (Du x))
          ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict (sphere a r)) ∧
        Integrable (fun x => hsNormSq (Dv x))
          ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict (sphere a r)) ∧
        (∫ θ : sphere (0 : Domain n) 1, hsNormSq
          (fun i => (sphereGradient hn (fun θ => u (a + r • θ.val)) huR i) θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Du x)
            ∂Measure.euclideanHausdorffMeasure (n - 1) ∧
        (∫ θ : sphere (0 : Domain n) 1, hsNormSq
          (fun i => (sphereGradient hn (fun θ => v (a + r • θ.val)) hvR i) θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Dv x)
            ∂Measure.euclideanHausdorffMeasure (n - 1)
  have hR : 0 < R := hs.trans hsR
  have hsub : Ioo s R ⊆ Ioo (0 : ℝ) R := fun _ hr => ⟨hs.trans hr.1, hr.2⟩
  have hQ : ∀ᵐ r ∂volume.restrict (Ioo s R), Q r := by
    have huSl := (ae_sphereSobolev_and_gradientEnergy hn hu hR hball).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hvSl := (ae_sphereSobolev_and_gradientEnergy hn hv hR hball).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have huT := (ae_sphereSobolev_and_targetValues hn hu huN hR hball).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hvT := (ae_sphereSobolev_and_targetValues hn hv hvN hR hball).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hP, huSl, hvSl, huT, hvT] with r hPr hur hvr huNr hvNr
    obtain ⟨huR, huI, hDuI, hEu⟩ := hur
    obtain ⟨hvR, hvI, hDvI, hEv⟩ := hvr
    exact ⟨hPr, huR, hvR, huNr.2, hvNr.2, huI, hvI, hDuI, hDvI, hEu, hEv⟩
  have henergy : IntegrableOn
      (fun x => hsNormSq (Du x) + hsNormSq (Dv x)) (ball a R) :=
    (hu.integrable_hsNormSq_ball hball).add (hv.integrable_hsNormSq_ball hball)
  have hdiff : IntegrableOn (fun x => ‖u x - v x‖ ^ 2) (ball a R) :=
    (((hu.memW12_ball hball).2.1).sub ((hv.memW12_ball hball).2.1)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  obtain ⟨r, hr, hqr, _hEI, hDI, hE, hD⟩ := exists_polar_good_radius_with_property
    (by omega : 0 < n) hs hsR henergy hdiff
    (fun x => add_nonneg (hsNormSq_nonneg (Du x)) (hsNormSq_nonneg (Dv x)))
    (fun x => sq_nonneg ‖u x - v x‖) hQ
  obtain ⟨hPr, huR, hvR, huNr, hvNr, hGuI, hGvI, hDuI, hDvI, hGu, hGv⟩ := hqr
  have hrpos : 0 < r := hs.trans hr.1
  let ρ : PositiveRadius := ⟨r, hrpos⟩
  have hnative := euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)
  have hDuAng : Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Du (a + r • θ.val)))
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) :=
    (integrable_euclidean_sphereArea_affine_iff hn a ρ (fun x => hsNormSq (Du x))).mp hDuI
  have hDvAng : Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Dv (a + r • θ.val)))
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) :=
    (integrable_euclidean_sphereArea_affine_iff hn a ρ (fun x => hsNormSq (Dv x))).mp hDvI
  rw [← hnative] at hDI hE hD
  refine ⟨r, hr, hPr, huR, hvR, huNr, hvNr, hGuI.add hGvI, hDI, ?_, hD⟩
  have hsum := add_le_add hGu hGv
  rw [← integral_add hGuI hGvI, ← mul_add] at hsum
  rw [integral_euclidean_sphereArea_affine hn a ρ (fun x => hsNormSq (Du x)),
    integral_euclidean_sphereArea_affine hn a ρ (fun x => hsNormSq (Dv x))] at hsum
  change _ ≤ r ^ (3 - (n : ℤ)) *
    (r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
      ∂Measure.euclideanHausdorffMeasure (n - 1)) +
    r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1, hsNormSq (Dv (a + r • θ.val))
      ∂Measure.euclideanHausdorffMeasure (n - 1))) at hsum
  rw [← mul_add, ← integral_add hDuAng hDvAng] at hsum
  have hscale : r ^ ((n : ℤ) - 3) * r ^ (3 - (n : ℤ)) = 1 := by
    rw [← zpow_add₀ hrpos.ne']
    simp only [sub_add_sub_cancel, sub_self, zpow_zero]
  have hbound := mul_le_mul_of_nonneg_left hsum (zpow_nonneg hrpos.le ((n : ℤ) - 3))
  rw [← mul_assoc, hscale, one_mul] at hbound
  exact hbound.trans hE

end StratificationTheory.Compactness
