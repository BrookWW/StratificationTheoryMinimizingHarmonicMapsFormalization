module
public import StratificationTheory.Foundation.CylinderTimeTests
public import StratificationTheory.Foundation.CylinderSobolevCollar
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public section
open HarmonicMaps MeasureTheory Set
open scoped ContDiff
namespace StratificationTheory

private theorem cylinder_inverse_integrable {n q : ℕ} (U : OpenDomain n) {a b : ℝ}
    {w : Domain (n + 1) → Ambient q}
    (hw : IntegrableOn w {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
      (n := n) (m := 1) y).1 ∈ U.val ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b}) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    Integrable (fun p : Domain n × ℝ =>
      w (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      ((volume.restrict U.val).prod (volume.restrict (Ioo a b))) := by
  intro e
  let Ω := {y : Domain (n + 1) | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b}
  have hΩ : MeasurableSet Ω :=
    (U.property.preimage (continuous_fst.comp e.continuous)).measurableSet.inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous))).measurableSet
  have hp := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hΩ
  have hpre : (fun p : Domain n × ℝ => e.symm
      (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ⁻¹' Ω = U.val ×ˢ Ioo a b := by
    ext p
    simp [Ω]
  rw [hpre, ← Measure.prod_restrict] at hp
  exact hp.integrable_comp_of_integrable hw

private theorem cylinder_weighted_integrable {n q : ℕ} (U : OpenDomain n) {a b : ℝ}
    {F : Domain n × ℝ → Ambient q} (hF : Integrable F
      ((volume.restrict U.val).prod (volume.restrict (Ioo a b))))
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun p : Domain n × ℝ => φ p.2 • F p)
      ((volume.restrict U.val).prod (volume.restrict (Ioo a b))) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hcφ
  exact hF.bdd_smul C (hφ.comp continuous_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hC p.2)

theorem MemW12.cylinder_time_test_ae {n q : ℕ} (U : OpenDomain n)
    (hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤) {a b : ℝ}
    {w : Domain (n + 1) → Ambient q} {Dw : Domain (n + 1) → Gradient (n + 1) q}
    (hw : MemW12
      ⟨{y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp
              (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)))⟩ w Dw)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ᵐ x ∂volume.restrict U.val,
      IntegrableOn (fun t => w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) (Ioo a b) ∧
      IntegrableOn (fun t => Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
        (Fin.natAdd n (0 : Fin 1))) (Ioo a b) ∧
      IntegrableOn (fun t => deriv φ t • w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) (Ioo a b) ∧
      (∫ t in Ioo a b, deriv φ t • w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) = 0 := by
  intro e
  let Ω := {y : Domain (n + 1) | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b}
  let μ := (volume : Measure (Domain n)).restrict U.val
  let ν := (volume : Measure ℝ).restrict (Ioo a b)
  have hΩfin : (volume : Measure (Domain (n + 1))) Ω ≠ ⊤ := by
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure ((volume : Measure (Domain (n + 1))).restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩfin
  have hwint : IntegrableOn w Ω := MemLp.integrable (by norm_num) hw.2.1
  have hDint : IntegrableOn (fun y => Dw y (Fin.natAdd n (0 : Fin 1))) Ω :=
    MemLp.integrable (by norm_num) (hw.2.2 (Fin.natAdd n (0 : Fin 1)))
  let W : Domain n × ℝ → Ambient q := fun p =>
    w (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  let D : Domain n × ℝ → Ambient q := fun p =>
    Dw (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) (Fin.natAdd n (0 : Fin 1))
  have hW : Integrable W (μ.prod ν) := cylinder_inverse_integrable U hwint
  have hD : Integrable D (μ.prod ν) := cylinder_inverse_integrable U hDint
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  let A : Domain n × ℝ → Ambient q := fun p => deriv φ p.2 • W p
  let B : Domain n × ℝ → Ambient q := fun p => φ p.2 • D p
  let F : Domain n × ℝ → Ambient q := fun p => A p + B p
  let H : Domain n → Ambient q := fun x => ∫ t, F (x, t) ∂ν
  have hA : Integrable A (μ.prod ν) := cylinder_weighted_integrable U hW hφ' hcφ.deriv
  have hB : Integrable B (μ.prod ν) := cylinder_weighted_integrable U hD hφ.continuous hcφ
  have hF : Integrable F (μ.prod ν) := hA.add hB
  have hH : Integrable H μ := hF.integral_prod_left
  have hzero : ∀ᵐ x ∂μ, x ∈ U.val → H x = 0 := by
    apply U.property.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hH.locallyIntegrable.locallyIntegrableOn U.val)
    intro ψ hψ hcψ hsψ
    obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hcψ
    have hψA : Integrable (fun p => ψ p.1 • A p) (μ.prod ν) :=
      hA.bdd_smul C (hψ.continuous.comp continuous_fst).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => hC p.1)
    have hψB : Integrable (fun p => ψ p.1 • B p) (μ.prod ν) :=
      hB.bdd_smul C (hψ.continuous.comp continuous_fst).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => hC p.1)
    have hψF : Integrable (fun p => ψ p.1 • F p) (μ.prod ν) :=
      hF.bdd_smul C (hψ.continuous.comp continuous_fst).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => hC p.1)
    have hid := HasWeakGradient.cylinder_separable_time_identity U hw.1
      hψ hcψ hsψ hφ hcφ hsφ
    have hcoord := (measurePreserving_cylinder_coordinates n).restrict_preimage
      (U.property.measurableSet.prod (measurableSet_Ioo (a := a) (b := b)))
    rw [← Measure.prod_restrict] at hcoord
    let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
    let c := e.trans (ContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (Domain n)) τ)
    have hemb : MeasurableEmbedding (fun y : Domain (n + 1) => ((e y).1, (e y).2 0)) :=
      c.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hca := hcoord.integral_comp hemb (fun p => ψ p.1 • A p)
    have hcb := hcoord.integral_comp hemb (fun p => ψ p.1 • B p)
    have hinv := cylinder_coordinates_inverse_left n
    have hia : (∫ p, ψ p.1 • A p ∂(μ.prod ν)) =
        ∫ y in Ω, (ψ (e y).1 * deriv φ ((e y).2 0)) • w y := by
      rw [← hca]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change ψ (e y).1 • (deriv φ ((e y).2 0) •
          w (e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)))) = _
        rw [show e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = y
          from hinv y]
        exact (mul_smul _ _ _).symm
    have hib : (∫ p, ψ p.1 • B p ∂(μ.prod ν)) =
        ∫ y in Ω, (ψ (e y).1 * φ ((e y).2 0)) • Dw y (Fin.natAdd n (0 : Fin 1)) := by
      rw [← hcb]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change ψ (e y).1 • (φ ((e y).2 0) •
          Dw (e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)))
            (Fin.natAdd n (0 : Fin 1))) = _
        rw [show e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = y
          from hinv y]
        exact (mul_smul _ _ _).symm
    calc
      (∫ x, ψ x • H x ∂μ) = ∫ p, ψ p.1 • F p ∂(μ.prod ν) := by
        rw [integral_prod _ hψF]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => (integral_smul (ψ x) _).symm
      _ = (∫ p, ψ p.1 • A p ∂(μ.prod ν)) +
          ∫ p, ψ p.1 • B p ∂(μ.prod ν) := by
        simp only [F, smul_add, integral_add hψA hψB]
      _ = 0 := by rw [hia, hib, hid]; exact neg_add_cancel _
  filter_upwards [hW.prod_right_ae, hD.prod_right_ae, hF.prod_right_ae, hzero,
    ae_restrict_mem U.property.measurableSet] with x hxW hxD hxF hxzero hxU
  exact ⟨hxW, hxD, hxF, hxzero hxU⟩
theorem MemW12.radial_collar_time_test_ae {n q : ℕ} (U : OpenDomain n)
    {δ : ℝ} (hU : U.val = {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ}) {a b : ℝ}
    {w : Domain (n + 1) → Ambient q} {Dw : Domain (n + 1) → Gradient (n + 1) q}
    (hw : MemW12
      ⟨{y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp
              (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)))⟩ w Dw)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ᵐ x ∂volume.restrict U.val,
      IntegrableOn (fun t => w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) (Ioo a b) ∧
      IntegrableOn (fun t => Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
        (Fin.natAdd n (0 : Fin 1))) (Ioo a b) ∧
      IntegrableOn (fun t => deriv φ t • w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) (Ioo a b) ∧
      (∫ t in Ioo a b, deriv φ t • w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) = 0 := by
  have hsub : U.val ⊆ Metric.ball (0 : Domain n) (1 + δ) := by
    intro x hx
    exact mem_ball_zero_iff.mpr ((hU ▸ hx).2)
  have hfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top).ne
  exact MemW12.cylinder_time_test_ae U hfinite hw hφ hcφ hsφ

theorem MemCylinderW12.exists_radial_collar_time_tests {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) {v : unitCylinder n a b → Ambient q}
    (hv : MemCylinderW12 hn hab v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∃ U : OpenDomain n,
        U.val = {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} ∧
        Metric.sphere (0 : Domain n) 1 ⊆ U.val ∧ (0 : Domain n) ∉ U.val ∧
        ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
          MemW12 ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
            (U.property.preimage (continuous_fst.comp e.continuous)).inter
              (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
                (continuous_snd.comp e.continuous)))⟩ w Dw ∧
          (∀ (ρ : PositiveRadius) (c : unitCylinder n a b),
            (e c.val).2 0 ∈ Ioo a b → ρ.val • (e c.val).1 ∈ U.val →
              w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = v c) ∧
          ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo a b →
              ∀ᵐ x ∂volume.restrict U.val,
      IntegrableOn (fun t => w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) (Ioo a b) ∧
      IntegrableOn (fun t => Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
        (Fin.natAdd n (0 : Fin 1))) (Ioo a b) ∧
      IntegrableOn (fun t => deriv φ t • w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) (Ioo a b) ∧
      (∫ t in Ioo a b, deriv φ t • w (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) = 0 := by
  intro e
  obtain ⟨_hLp, δ, hδ, hδsmall, U, hU, hSphere, hzero, w, Dw, hW, hraw⟩ :=
    (memCylinderW12_iff_exists_radial_collar hn hab v).mp hv
  refine ⟨δ, hδ, hδsmall, U, hU, hSphere, hzero, w, Dw, hW, hraw, ?_⟩
  intro φ hφ hcφ hsφ
  exact MemW12.radial_collar_time_test_ae U hU hW hφ hcφ hsφ
end StratificationTheory
