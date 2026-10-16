module

public import StratificationTheory.Frozen.SphereGradientCharacterization
public import StratificationTheory.Interpolation.CylinderAffineGradient
public import StratificationTheory.Interpolation.LinearCylinderEnergy
import StratificationTheory.Foundation.CylinderIntegralTransport

/-!
# Native energy of an actual affine cylinder weak extension

The named sphere gradients supply coherent radial maps and weak columns on
the punctured space. Restriction to one fixed annulus gives finite Sobolev
data. Their affine cylinder extension has the corresponding named angular
columns on one common full-measure set of directions, at every time. The
native surface-product identity then transfers the energy of this same weak
gradient, with spatial coefficient `(b - a) / 2` and temporal coefficient
`(b - a)⁻¹`.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory

/-- The full named-gradient characterization supplies coherent radial data
that are finite on the fixed annulus, with all original raw rays and every
positive-radius angular weak-column identity retained. -/
theorem exists_sphereGradient_finite_annulus_data {n q : ℕ} (hn : 2 ≤ n)
    (v : sphere (0 : Domain n) 1 → Ambient q) (hv : MemSphereW12 hn v) :
    let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
    ∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
      MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D ∧
      MemW12 U w D ∧
      (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ) ∧
      ∀ (ρ : PositiveRadius) (i : Fin n),
        (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))]
          (fun θ => (sphereGradient hn v hv i) θ) := by
  intro U
  obtain ⟨w, D, hW, hraw, hscale⟩ := (sphereGradient_characterization hn v hv).1.1
  let K := {x : Domain n | 1 / 2 ≤ ‖x‖} ∩ closedBall (0 : Domain n) 2
  have hK : IsCompact K := (isCompact_closedBall (0 : Domain n) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter isClosed_closedBall) inter_subset_right
  have hKsub : K ⊆ ({0}ᶜ : Set (Domain n)) := by
    intro x hx
    change x ≠ 0
    intro hx0
    have hlo : (1 / 2 : ℝ) ≤ ‖x‖ := hx.1
    rw [hx0, norm_zero] at hlo
    norm_num at hlo
  have hUK : U.val ⊆ K := fun x hx =>
    ⟨hx.1.le, mem_closedBall_zero_iff.mpr hx.2.le⟩
  have hfinite : MemW12 U w D :=
    ⟨hW.1.mono (hUK.trans hKsub),
      (hW.2.1 K hK hKsub).mono_measure (Measure.restrict_mono_set volume hUK),
      fun i => (hW.2.2 i K hK hKsub).mono_measure (Measure.restrict_mono_set volume hUK)⟩
  exact ⟨w, D, hW, hfinite, hraw, hscale⟩

/-- Two actual sphere Sobolev maps give one full finite cylinder weak
extension whose native angular columns are their named sphere gradients.
One full-measure angular set works simultaneously for all real times and
all spatial and temporal columns. -/
theorem exists_cylinder_affine_named_gradient {n q : ℕ} (hn : 2 ≤ n)
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
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, Dw (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
              ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
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
  have huUnit (θ : sphere (0 : Domain n) 1) : fu θ.val = u θ := by
    simpa only [one_smul] using huRaw ⟨1, by norm_num⟩ θ
  have hvUnit (θ : sphere (0 : Domain n) 1) : fv θ.val = v θ := by
    simpa only [one_smul] using hvRaw ⟨1, by norm_num⟩ θ
  have hDu : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)), ∀ i : Fin n, Du θ.val i = (sphereGradient hn u hu i) θ := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [huScale ⟨1, by norm_num⟩ i] with θ hθ
    simpa only [one_smul] using hθ
  have hDv : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)), ∀ i : Fin n, Dv θ.val i = (sphereGradient hn v hv i) θ := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hvScale ⟨1, by norm_num⟩ i] with θ hθ
    simpa only [one_smul] using hθ
  refine ⟨w, Dw, MemW12.cylinder_affine_gradient U hUfinite hab huW hvW, ?_, ?_⟩
  · intro ρ c _ht _hx
    change (1 - ((e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).2 0 - a) / (b - a)) •
        fu (e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).1 +
      (((e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).2 0 - a) / (b - a)) •
        fv (e (e.symm (ρ.val • (e c.val).1, (e c.val).2))).1 = _
    rw [e.apply_symm_apply, huRaw ρ ⟨(e c.val).1, c.property.1⟩,
      hvRaw ρ ⟨(e c.val).1, c.property.1⟩]
  · filter_upwards [hDu, hDv] with θ hθu hθv
    intro t
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Dw, α, e.apply_symm_apply, Fin.addCases_left, PiLp.single_apply,
        ite_true, hθu, hθv]
    · simp only [Dw, e.apply_symm_apply, Fin.addCases_right, huUnit, hvUnit]

/-- The same actual finite weak cylinder extension has a native physical
HS-energy bound expressed in the original named sphere gradients and raw
endpoint discrepancy. The weak gradient is identified before transporting
its energy to the native physical cylinder measure. -/
theorem exists_cylinder_affine_native_energy {n q : ℕ} (hn : 2 ≤ n)
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
      (∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, Dw (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
              ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      Integrable (fun c : unitCylinder n a b => hsNormSq (Dw c.val))
        (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      (∫ c : unitCylinder n a b, hsNormSq (Dw c.val) ∂Measure.euclideanHausdorffMeasure n) ≤
        ((b - a) / 2) *
          (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
          (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
            ∂Measure.euclideanHausdorffMeasure (n - 1)) := by
  intro e U
  obtain ⟨w, Dw, hW, hraw, hD⟩ := exists_cylinder_affine_named_gradient hn hab u v hu hv
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let μ := σ.prod (volume.restrict (Icc a b))
  let Gu : sphere (0 : Domain n) 1 → Fin n → Ambient q :=
    fun θ i => (sphereGradient hn u hu i) θ
  let Gv : sphere (0 : Domain n) 1 → Fin n → Ambient q :=
    fun θ i => (sphereGradient hn v hv i) θ
  let E : sphere (0 : Domain n) 1 × ℝ → ℝ := fun p =>
    (∑ i : Fin n, ‖(1 - (p.2 - a) / (b - a)) • Gu p.1 i +
      ((p.2 - a) / (b - a)) • Gv p.1 i‖ ^ 2) +
      ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2
  let F : sphere (0 : Domain n) 1 × ℝ → ℝ := fun p =>
    hsNormSq (Dw (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)))
  have henergy := native_linear_cylinder_field_energy hab hu.1 hv.1
    (fun i => Lp.memLp (sphereGradient hn u hu i))
    (fun i => Lp.memLp (sphereGradient hn v hv i))
  have hFE : F =ᵐ[μ] E := by
    have hp : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
        ∀ t : ℝ, Dw (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • Gu p.1 i + ((t - a) / (b - a)) • Gv p.1 i)
            (fun _ => (b - a)⁻¹ • (v p.1 - u p.1)) :=
      Measure.quasiMeasurePreserving_fst.ae hD
    filter_upwards [hp] with p hp
    dsimp only [F]
    rw [hp p.2]
    simp only [hsNormSq, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Fin.sum_univ_one, E]
  have hFI : Integrable F μ := henergy.1.congr hFE.symm
  have htransport := integrable_unitCylinder_of_param_and_integral (by omega : 0 < n)
    (fun c : unitCylinder n a b => hsNormSq (Dw c.val)) F hFI (fun _ _ => rfl)
  refine ⟨w, Dw, hW, hraw, hD, htransport.1, ?_⟩
  calc
    (∫ c : unitCylinder n a b, hsNormSq (Dw c.val) ∂Measure.euclideanHausdorffMeasure n) =
        ∫ p, F p ∂μ := htransport.2
    _ = ∫ p, E p ∂μ := integral_congr_ae hFE
    _ ≤ _ := henergy.2.2.2

end StratificationTheory
