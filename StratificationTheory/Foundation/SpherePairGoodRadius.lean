module

public import StratificationTheory.Foundation.PolarGoodRadius
public import StratificationTheory.Frozen.SphereSliceEnergy

/-!
# One common good Sobolev sphere

Both original maps, their target values and their named sphere-gradient
energy bounds occur at the same radius that controls the two annular averages.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- Two actual target-valued locally Sobolev maps have one admissible radius
with complete named-gradient slice data and both annular mean bounds. -/
theorem exists_sphereSobolev_pair_good_radius {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    (huN : TakesValuesIn N Ω u) (hvN : TakesValuesIn N Ω v)
    {a : Domain n} {s R : ℝ} (hball : closedBall a R ⊆ Ω.val)
    (hs : 0 < s) (hsR : s < R) :
    ∃ r ∈ Ioo s R,
      (∃ huR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)),
        ∃ hvR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)),
          TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
          TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)) ∧
          Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
            (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) huR i) θ))
              (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
          Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
            (fun i => (sphereGradient hn (fun η => v (a + r • η.val)) hvR i) θ))
              (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
          Integrable (fun x => hsNormSq (Du x))
            ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict (sphere a r)) ∧
          Integrable (fun x => hsNormSq (Dv x))
            ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict (sphere a r)) ∧
          (∫ θ : sphere (0 : Domain n) 1, hsNormSq
            (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) huR i) θ)
              ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
            r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Du x)
              ∂Measure.euclideanHausdorffMeasure (n - 1) ∧
          (∫ θ : sphere (0 : Domain n) 1, hsNormSq
            (fun i => (sphereGradient hn (fun η => v (a + r • η.val)) hvR i) θ)
              ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
            r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Dv x)
              ∂Measure.euclideanHausdorffMeasure (n - 1)) ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        hsNormSq (Du (a + r • θ.val)) + hsNormSq (Dv (a + r • θ.val)))
          (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2)
          (volume : Measure (Domain n)).toSphere ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1,
        hsNormSq (Du (a + r • θ.val)) + hsNormSq (Dv (a + r • θ.val))
          ∂(volume : Measure (Domain n)).toSphere) ≤
            2 * (∫ x in ball a R \ ball a s, hsNormSq (Du x) + hsNormSq (Dv x)) / (R - s) ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1,
        ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2
          ∂(volume : Measure (Domain n)).toSphere) ≤
            2 * (∫ x in ball a R \ ball a s, ‖u x - v x‖ ^ 2) / (R - s) := by
  let P : ℝ → Prop := fun r =>
    ∃ huR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)),
        ∃ hvR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)),
          TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
          TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)) ∧
          Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
            (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) huR i) θ))
              (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
          Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
            (fun i => (sphereGradient hn (fun η => v (a + r • η.val)) hvR i) θ))
              (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
          Integrable (fun x => hsNormSq (Du x))
            ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict (sphere a r)) ∧
          Integrable (fun x => hsNormSq (Dv x))
            ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict (sphere a r)) ∧
          (∫ θ : sphere (0 : Domain n) 1, hsNormSq
            (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) huR i) θ)
              ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
            r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Du x)
              ∂Measure.euclideanHausdorffMeasure (n - 1) ∧
          (∫ θ : sphere (0 : Domain n) 1, hsNormSq
            (fun i => (sphereGradient hn (fun η => v (a + r • η.val)) hvR i) θ)
              ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
            r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Dv x)
              ∂Measure.euclideanHausdorffMeasure (n - 1)
  have hR : 0 < R := hs.trans hsR
  have hsub : Ioo s R ⊆ Ioo (0 : ℝ) R := fun _ hr => ⟨hs.trans hr.1, hr.2⟩
  have hPfull : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), P r := by
    filter_upwards [ae_sphereSobolev_and_gradientEnergy hn hu hR hball,
      ae_sphereSobolev_and_gradientEnergy hn hv hR hball,
      ae_sphereSobolev_and_targetValues hn hu huN hR hball,
      ae_sphereSobolev_and_targetValues hn hv hvN hR hball] with r hur hvr huNr hvNr
    obtain ⟨huR, huI, hDuI, hEu⟩ := hur
    obtain ⟨hvR, hvI, hDvI, hEv⟩ := hvr
    exact ⟨huR, hvR, huNr.2, hvNr.2, huI, hvI, hDuI, hDvI, hEu, hEv⟩
  have hP : ∀ᵐ r ∂volume.restrict (Ioo s R), P r :=
    hPfull.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have henergy : IntegrableOn
      (fun x : Domain n => hsNormSq (Du x) + hsNormSq (Dv x)) (ball a R) volume :=
    (hu.integrable_hsNormSq_ball hball).add (hv.integrable_hsNormSq_ball hball)
  have hdiffClosed : IntegrableOn (fun x : Domain n => ‖u x - v x‖ ^ 2) (closedBall a R) :=
    ((hu.2.1 (closedBall a R) (isCompact_closedBall a R) hball).sub
      (hv.2.1 (closedBall a R) (isCompact_closedBall a R) hball)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  exact exists_polar_good_radius_with_property (by omega : 0 < n) hs hsR
    henergy (hdiffClosed.mono_set ball_subset_closedBall)
    (fun x => add_nonneg (hsNormSq_nonneg (Du x)) (hsNormSq_nonneg (Dv x)))
    (fun x => sq_nonneg ‖u x - v x‖) hP

end StratificationTheory
