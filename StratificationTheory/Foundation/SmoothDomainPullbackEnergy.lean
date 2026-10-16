module

public import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
public import StratificationTheory.Foundation.CubicalConeGradientBound

/-!
# Native energy of the same smooth-coordinate weak pair

The original columns give the actual chain-rule weak pair, its quantitative
native energy bound and every original almost-everywhere value constraint.
The dimension and differential bound are the only column-estimate factors.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff BigOperators
namespace StratificationTheory

private theorem norm_sum_smul_sq_le_bound_energy {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Fin n → ℝ) (v : Fin n → E)
    (L : ℝ) (ha : ∀ j, |a j| ≤ |L|) :
    ‖∑ j : Fin n, a j • v j‖ ^ 2 ≤ L ^ 2 * (n : ℝ) * ∑ j, ‖v j‖ ^ 2 := by
  have hnorm : ‖∑ j : Fin n, a j • v j‖ ≤ |L| * ∑ j, ‖v j‖ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)
  calc
    _ ≤ (|L| * ∑ j, ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = L ^ 2 * (∑ j, ‖v j‖) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ L ^ 2 * ((n : ℝ) * ∑ j, ‖v j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin n => ‖v j‖))
        (sq_nonneg L)
    _ = _ := by rw [mul_assoc]

private theorem hsNormSq_smooth_domain_columns_le {m n q : ℕ}
    (F : Domain m → Domain n) (x : Domain m) (A : Gradient n q)
    (L : ℝ) (hDF : ‖fderiv ℝ F x‖ ≤ L) :
    hsNormSq (fun i => ∑ j : Fin n,
      (fderiv ℝ F x (EuclideanSpace.single i 1)) j • A j) ≤
      ((m : ℝ) * (n : ℝ) * L ^ 2) * hsNormSq A := by
  have hcoeff (i : Fin m) (j : Fin n) :
      |(fderiv ℝ F x (EuclideanSpace.single i 1)) j| ≤ |L| := by
    have he : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
      simpa only [norm_one] using PiLp.norm_single 2 (fun _ : Fin m => ℝ) i (1 : ℝ)
    calc
      _ ≤ ‖fderiv ℝ F x (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ j
      _ ≤ ‖fderiv ℝ F x‖ * ‖EuclideanSpace.single i 1‖ := (fderiv ℝ F x).le_opNorm _
      _ = ‖fderiv ℝ F x‖ := by rw [he, mul_one]
      _ ≤ |L| := hDF.trans (le_abs_self L)
  calc
    _ ≤ ∑ _i : Fin m, L ^ 2 * (n : ℝ) * hsNormSq A :=
      Finset.sum_le_sum fun i _ =>
        norm_sum_smul_sq_le_bound_energy _ A L (hcoeff i)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Actual native energy and arbitrary original a.e. value constraints hold
for the same original chain-rule pair, with the stated measure distortion. -/
theorem memW12_smooth_open_domain_pullback_energy {m n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (U : OpenDomain m)
    (F : Domain m → Domain n) (hF : ContDiffOn ℝ ∞ F U.val)
    (hFU : MapsTo F U.val Ω.val)
    (L : ℝ) (hDF : ∀ x ∈ U.val, ‖fderiv ℝ F x‖ ≤ L)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hmap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict Ω.val) :
    let W := u ∘ F
    let D : Domain m → Gradient m q := fun x i =>
      ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • Du (F x) j
    MemW12 U W D ∧
      (∀ x ∈ U.val, hsNormSq (D x) ≤
        ((m : ℝ) * (n : ℝ) * L ^ 2) * hsNormSq (Du (F x))) ∧
      dirichletEnergy D U.val ≤ ENNReal.ofReal ((m : ℝ) * (n : ℝ) * L ^ 2) *
        c * dirichletEnergy Du Ω.val ∧
      ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict Ω.val, P (u y)) →
        ∀ᵐ x ∂volume.restrict U.val, P (W x) := by
  intro W D
  have hW : MemW12 U W D := memW12_smooth_open_domain_pullback hu U F hF hFU L hDF c hc hmap
  have hpoint (x : Domain m) (hx : x ∈ U.val) : hsNormSq (D x) ≤
      ((m : ℝ) * (n : ℝ) * L ^ 2) * hsNormSq (Du (F x)) :=
    hsNormSq_smooth_domain_columns_le F x (Du (F x)) L (hDF x hx)
  have hFm : AEMeasurable F (volume.restrict U.val) :=
    hF.continuousOn.aemeasurable U.property.measurableSet
  have hAC := Measure.absolutelyContinuous_of_le_smul hmap
  refine ⟨hW, hpoint, ?_, fun _ hP => ae_of_ae_map hFm (hP.filter_mono hAC.ae_le)⟩
  let C : ℝ≥0∞ := ENNReal.ofReal ((m : ℝ) * (n : ℝ) * L ^ 2)
  let g : Domain n → ℝ≥0∞ := fun y => ENNReal.ofReal (hsNormSq (Du y))
  have hg : AEMeasurable g (volume.restrict Ω.val) :=
    hu.integrable_hsNormSq.aemeasurable.ennreal_ofReal
  have hgmap : AEMeasurable g (Measure.map F (volume.restrict U.val)) :=
    hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)
  calc
    dirichletEnergy D U.val ≤ ∫⁻ x in U.val, C * g (F x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
      change ENNReal.ofReal (hsNormSq (D x)) ≤
        ENNReal.ofReal ((m : ℝ) * (n : ℝ) * L ^ 2) * ENNReal.ofReal (hsNormSq (Du (F x)))
      rw [← ENNReal.ofReal_mul (show 0 ≤ (m : ℝ) * (n : ℝ) * L ^ 2 by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpoint x hx)
    _ = C * ∫⁻ x in U.val, g (F x) := lintegral_const_mul' C _ ENNReal.ofReal_ne_top
    _ = C * ∫⁻ y, g y ∂Measure.map F (volume.restrict U.val) := by
      rw [lintegral_map' hgmap hFm]
    _ ≤ C * ∫⁻ y, g y ∂(c • volume.restrict Ω.val) :=
      mul_le_mul' le_rfl (lintegral_mono' hmap le_rfl)
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, mul_assoc]; rfl

end StratificationTheory
