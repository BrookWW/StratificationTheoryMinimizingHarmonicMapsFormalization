module

public import StratificationTheory.Interpolation.AffineCylinderPostcompositionEnergy
public import StratificationTheory.Interpolation.ProjectedCollar
public import StratificationTheory.Foundation.CylinderTracePostcomposition
public import StratificationTheory.Foundation.CylinderTraceAlgebra

/-!
# Projection of the actual affine cylinder connector

A single target projection gives full weak data, native energy and named
closed-interval traces for every affine connector lying in its tube.
The native columns are tied to the named endpoint gradients of the same map.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff
namespace StratificationTheory.Interpolation

/-- One target-dependent projection controls the actual affine extension and
its native chain-rule energy, retains target values at every trace time, and
fixes each target-valued endpoint class. The tube input is a bound on the
original affine map, with no gradient or trace conclusions assumed. -/
theorem exists_projected_affine_cylinder_operator {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q),
      0 < ρ ∧ ContDiff ℝ ∞ Q ∧ (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (hab : a < b)
        (u v : sphere (0 : Domain n) 1 → Ambient q)
        (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v),
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let c : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      infDist (c y) N.carrierSet < ρ) →
    ∃ w : Domain (n + 1) → Ambient q, ∃ D : Domain (n + 1) → Gradient (n + 1) q,
      MemW12 Ω w D ∧
      (∀ (ρ : PositiveRadius) (y : unitCylinder n a b),
        (e y.val).2 0 ∈ Ioo a b → ρ.val • (e y.val).1 ∈ U.val →
          w (e.symm (ρ.val • (e y.val).1, (e y.val).2)) = c y) ∧
      (∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, D (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
              ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      (∀ ρ : PositiveRadius, ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, D (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn u hu i) θ) +
              ((t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn v hv i) θ))
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      MemW12 Ω (Q ∘ w) (fun x i => fderiv ℝ Q (w x) (D x i)) ∧
      (∀ (ρ : PositiveRadius) (y : unitCylinder n a b),
        (e y.val).2 0 ∈ Ioo a b → ρ.val • (e y.val).1 ∈ U.val →
          (Q ∘ w) (e.symm (ρ.val • (e y.val).1, (e y.val).2)) = (Q ∘ c) y) ∧
      MemCylinderW12 hn hab (Q ∘ c) ∧
      (∀ i : Fin (n + 1), MemLp
        (fun y : unitCylinder n a b => fderiv ℝ Q (w y.val) (D y.val i)) 2
          (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) ∧
      Integrable (fun y : unitCylinder n a b =>
        hsNormSq (fun i => fderiv ℝ Q (w y.val) (D y.val i)))
          (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      (∫ y : unitCylinder n a b, hsNormSq (fun i => fderiv ℝ Q (w y.val) (D y.val i))
        ∂Measure.euclideanHausdorffMeasure n) ≤ 4 *
          (((b - a) / 2) * (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
            (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
              ∂Measure.euclideanHausdorffMeasure (n - 1))) ∧
      (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
        (Q ∘ c) y ∈ N.carrierSet) ∧
      ∃ hQc : MemCylinderW12 hn hab (Q ∘ c),
        (∀ t : Icc a b, ∀ᵐ θ : sphere (0 : Domain n) 1
          ∂Measure.euclideanHausdorffMeasure (n - 1),
            cylinderTrace hn hab (Q ∘ c) hQc t θ ∈ N.carrierSet) ∧
        ((∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
            u θ ∈ N.carrierSet) →
          cylinderTrace hn hab (Q ∘ c) hQc ⟨a, le_rfl, hab.le⟩ = hu.1.toLp u) ∧
        ((∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
            v θ ∈ N.carrierSet) →
          cylinderTrace hn hab (Q ∘ c) hQc ⟨b, hab.le, le_rfl⟩ = hv.1.toLp v) := by
  obtain ⟨ρ, Q, hρ, _hbase, hQ, ⟨L, _hL, hQL⟩, hfix, hnear⟩ :=
    exists_smooth_target_projection N
  refine ⟨ρ, Q, hρ, hQ, hfix, ?_⟩
  intro n hn a b hab u v hu hv e U Ω c htube
  have hvalues : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      (Q ∘ c) y ∈ N.carrierSet ∧ ‖fderiv ℝ Q (c y)‖ ≤ 2 := by
    filter_upwards [htube] with y hy
    obtain ⟨_ht, _heq, hmem, hD⟩ := hnear (c y) hy
    exact ⟨hmem, hD⟩
  have hbound : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      ‖fderiv ℝ Q (c y)‖ ≤ ((2 : NNReal) : ℝ) := hvalues.mono fun _ h => h.2
  obtain ⟨w, D, hW, hraw, hD, hAll, hQW, hQraw, hQc, hcols, hInt, hEnergy⟩ :=
    exists_affine_cylinder_postcomposition_energy hn hab u v hu hv Q hQ L hQL 2 hbound
  have htarget := hvalues.mono fun _ h => h.1
  refine ⟨w, D, hW, hraw, hD, hAll, hQW, hQraw, hQc, hcols, hInt,
    ?_, htarget, hQc, cylinderTrace_mem_closed hn hab (Q ∘ c) hQc N.isClosed htarget, ?_, ?_⟩
  · simpa only [NNReal.coe_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hEnergy
  · intro huN
    obtain ⟨hc, hT, hTa, _hTb, _hinc⟩ := cylinderTrace_linearInterpolation hn hab u v hu hv
    obtain ⟨hL, hEq⟩ := cylinderTrace_postcompose hn hab c hc Q hQ L hQL ⟨a, le_rfl, hab.le⟩
    rw [hEq]
    apply Lp.ext
    filter_upwards [hL.coeFn_toLp, hu.1.coeFn_toLp, huN] with θ hθ huθ hNθ
    have hpoint : cylinderTrace hn hab c hc ⟨a, le_rfl, hab.le⟩ θ = u θ := by
      rw [hTa]
      exact huθ
    exact hθ.trans ((congrArg Q hpoint).trans ((hfix _ hNθ).trans huθ.symm))
  · intro hvN
    obtain ⟨hc, hT, _hTa, hTb, _hinc⟩ := cylinderTrace_linearInterpolation hn hab u v hu hv
    obtain ⟨hL, hEq⟩ := cylinderTrace_postcompose hn hab c hc Q hQ L hQL ⟨b, hab.le, le_rfl⟩
    rw [hEq]
    apply Lp.ext
    filter_upwards [hL.coeFn_toLp, hv.1.coeFn_toLp, hvN] with θ hθ hvθ hNθ
    have hpoint : cylinderTrace hn hab c hc ⟨b, hab.le, le_rfl⟩ θ = v θ := by
      rw [hTb]
      exact hvθ
    exact hθ.trans ((congrArg Q hpoint).trans ((hfix _ hNθ).trans hvθ.symm))

end StratificationTheory.Interpolation
