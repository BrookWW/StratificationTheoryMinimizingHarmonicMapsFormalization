module

public import StratificationTheory.Interpolation.CylinderLinearNativeEnergy

/-!
# All-radius coherence of the actual affine cylinder weak gradient

The complete named sphere-gradient characterization supplies one global
punctured pair for each endpoint. The resulting finite weak extension retains
its spatial inverse-radius columns and constant temporal column at every
positive radius, on a common angular full-measure set for all real times.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- The same actual affine weak extension has the named spatial columns
with their full positive-radius scaling, and the original temporal difference.
These are statements about the coherent actual weak data, not arbitrary
ambient representatives restricted to the unit sphere. -/
theorem exists_cylinder_affine_all_radius_gradient {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
    ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
      MemW12
        ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩ w Dw ∧
      (∀ (ρ : PositiveRadius) (c : unitCylinder n a b),
        (e c.val).2 0 ∈ Ioo a b → ρ.val • (e c.val).1 ∈ U.val →
          w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) =
            (1 - ((e c.val).2 0 - a) / (b - a)) • u ⟨(e c.val).1, c.property.1⟩ +
              (((e c.val).2 0 - a) / (b - a)) • v ⟨(e c.val).1, c.property.1⟩) ∧
      ∀ ρ : PositiveRadius, ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, Dw (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn u hu i) θ) +
              ((t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn v hv i) θ))
            (fun _ => (b - a)⁻¹ • (v θ - u θ)) := by
  intro e U
  obtain ⟨fu, Du, _huLoc, huW, huRaw, huScale⟩ := exists_sphereGradient_finite_annulus_data hn u hu
  obtain ⟨fv, Dv, _hvLoc, hvW, hvRaw, hvScale⟩ := exists_sphereGradient_finite_annulus_data hn v hv
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := by
    have hsub : U.val ⊆ ball (0 : Domain n) 2 := fun x hx => mem_ball_zero_iff.mpr hx.2
    exact (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top).ne
  let α : Domain (n + 1) → ℝ := fun y => ((e y).2 0 - a) / (b - a)
  let w : Domain (n + 1) → Ambient q := fun y =>
    (1 - α y) • fu (e y).1 + α y • fv (e y).1
  let Dw : Domain (n + 1) → Gradient (n + 1) q := fun y =>
    Fin.addCases (fun i => (1 - α y) • Du (e y).1 i + α y • Dv (e y).1 i)
      (fun _ => (b - a)⁻¹ • (fv (e y).1 - fu (e y).1))
  have hDu (ρ : PositiveRadius) : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)), ∀ i : Fin n,
        Du (ρ.val • θ.val) i = ρ.val⁻¹ • (sphereGradient hn u hu i) θ := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [huScale ρ i] with θ hθ
    have h := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hθ
    simpa only [smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using h
  have hDv (ρ : PositiveRadius) : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)), ∀ i : Fin n,
        Dv (ρ.val • θ.val) i = ρ.val⁻¹ • (sphereGradient hn v hv i) θ := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hvScale ρ i] with θ hθ
    have h := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hθ
    simpa only [smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using h
  refine ⟨w, Dw, MemW12.cylinder_affine_gradient U hUfinite hab huW hvW, ?_, ?_⟩
  · intro ρ c _ht _hx
    change (1 - ((e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).2 0 - a) / (b - a)) •
        fu (e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).1 +
      (((e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).2 0 - a) / (b - a)) •
        fv (e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).1 = _
    rw [e.apply_symm_apply, huRaw ρ ⟨(e c.val).1, c.property.1⟩,
      hvRaw ρ ⟨(e c.val).1, c.property.1⟩]
  · intro ρ
    filter_upwards [hDu ρ, hDv ρ] with θ hθu hθv
    intro t
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Dw, α, e.apply_symm_apply, Fin.addCases_left, PiLp.single_apply,
        ite_true, hθu, hθv]
    · simp only [Dw, e.apply_symm_apply, Fin.addCases_right, huRaw, hvRaw]

end StratificationTheory
