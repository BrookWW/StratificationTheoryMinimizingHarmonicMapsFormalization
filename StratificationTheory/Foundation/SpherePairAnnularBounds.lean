module

public import StratificationTheory.Foundation.SpherePairGoodRadius
import StratificationTheory.Foundation.SphereSurfaceIntegral

/-!
# Native sphere-gradient bounds at one annular radius

The same target-valued Sobolev sphere controls both native named-gradient
energy and raw endpoint discrepancy by their actual annular integrals.
The inverse radial factor remains valid in dimension two.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- One common target-valued Sobolev sphere satisfies both scale-consistent
annular estimates, with the actual named gradients and original discrepancy. -/
theorem exists_sphereSobolev_pair_annular_bounds {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    (huN : TakesValuesIn N Ω u) (hvN : TakesValuesIn N Ω v)
    {a : Domain n} {s R : ℝ} (hball : closedBall a R ⊆ Ω.val)
    (hs : 0 < s) (hsR : s < R) :
    ∃ r ∈ Ioo s R,
      ∃ huR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)),
      ∃ hvR : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)),
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => v (a + r • θ.val)) ∧
        Integrable (fun θ : sphere (0 : Domain n) 1 =>
          hsNormSq (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) huR i) θ) +
          hsNormSq (fun i => (sphereGradient hn (fun η => v (a + r • η.val)) hvR i) θ))
            (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        Integrable (fun θ : sphere (0 : Domain n) 1 => ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2)
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        r ^ ((n : ℤ) - 3) * (∫ θ : sphere (0 : Domain n) 1,
          hsNormSq (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) huR i) θ) +
          hsNormSq (fun i => (sphereGradient hn (fun η => v (a + r • η.val)) hvR i) θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          2 * (∫ x in ball a R \ ball a s, hsNormSq (Du x) + hsNormSq (Dv x)) / (R - s) ∧
        r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1,
          ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          2 * (∫ x in ball a R \ ball a s, ‖u x - v x‖ ^ 2) / (R - s) := by
  obtain ⟨r, hr, hnamed, _hEI, hDI, hE, hD⟩ :=
    exists_sphereSobolev_pair_good_radius hn hu hv huN hvN hball hs hsR
  obtain ⟨huR, hvR, huNr, hvNr, hGuI, hGvI, hDuI, hDvI, hGu, hGv⟩ := hnamed
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
  refine ⟨r, hr, huR, hvR, huNr, hvNr, hGuI.add hGvI, hDI, ?_, hD⟩
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

end StratificationTheory
