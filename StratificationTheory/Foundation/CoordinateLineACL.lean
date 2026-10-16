module

public import StratificationTheory.Foundation.CoordinateSliceConvergence
public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import StratificationTheory.Foundation.IntervalWeakRepresentative
public import HarmonicMaps.Analysis.SobolevSmoothDensity
import StratificationTheory.Foundation.CylinderTimeTests
import StratificationTheory.Foundation.IntervalWeakDerivativeClosure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Absolutely continuous coordinate-line representatives

A smooth graph approximation on an actual Sobolev ball gives one common
subsequence for the function and its last weak column on almost every line
of a contained measurable rectangle. Interval weak-derivative closure
produces the absolutely continuous line and its exact integral increments.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff BigOperators
namespace StratificationTheory

private theorem smooth_curve_weakDerivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b)
    {f g : ℝ → E} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (hfg : ∀ x, HasDerivAt f (g x) x)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (_hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ t, deriv φ t • f t) = -(∫ t, φ t • g t) := by
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun hm => (lt_irrefl a) (hsφ hm).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun hm => (lt_irrefl b) (hsφ hm).2)
  have hid := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    hφ.continuous.continuousOn hf.continuous.continuousOn
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    (fun x _ => hfg x)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable a b)
    (hg.intervalIntegrable a b)
  rw [hφa, hφb, zero_smul, zero_smul, sub_self, zero_sub] at hid
  have hid' : (∫ t in a..b, deriv φ t • f t) = -(∫ t in a..b, φ t • g t) := by
    rw [hid, neg_neg]
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at hid'
  have hrestriction (ψ : ℝ → ℝ) (hs : tsupport ψ ⊆ Ioo a b) (F : ℝ → E) :
      (∫ t in Ioo a b, ψ t • F t) = ∫ t, ψ t • F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun hm => ht (hs hm)), zero_smul]
  rwa [hrestriction (deriv φ) (tsupport_deriv_subset.trans hsφ), hrestriction φ hsφ] at hid'

private theorem coordinateLine_affine {n : ℕ} (x : Domain n) (t : ℝ) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
      (x, EuclideanSpace.single (0 : Fin 1) t) =
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm (x, 0) +
      t • EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1 := by
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).injective
  rw [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, finAddEquivProd_time_basis]
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  congr 1
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp

/-- Actual finite Sobolev data on a ball admit absolutely continuous
representatives on almost every last-coordinate line of a contained rectangle.
The line increments integrate the original last weak-gradient column. -/
theorem ae_coordinateLine_exists_ac_of_memW12_ball {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ᵐ x ∂volume.restrict S,
      MemLp (fun t => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
        2 (volume.restrict (Ioo a b)) ∧
      MemLp (fun t => Du (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
        (Fin.natAdd n (0 : Fin 1))) 2 (volume.restrict (Ioo a b)) ∧
      ∃ F : ℝ → Ambient q, AbsolutelyContinuousOnInterval F a b ∧
        F =ᵐ[volume.restrict (Ioo a b)]
          (fun t => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          F t - F s = ∫ r in s..t,
            Du (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))
              (Fin.natAdd n (0 : Fin 1)) := by
  intro e
  let j : Fin (n + 1) := Fin.natAdd n (0 : Fin 1)
  let μ := (volume : Measure (Domain n)).restrict S
  let ν := (volume : Measure ℝ).restrict (Ioo a b)
  let Ω := {y : Domain (n + 1) | (e y).1 ∈ S ∧ (e y).2 0 ∈ Ioo a b}
  have hΩ : MeasurableSet Ω :=
    (hS.preimage (continuous_fst.comp e.continuous).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)).measurable)
  have hΩsub : Ω ⊆ ball z R := by
    intro y hy
    have h := hrect (e y).1 hy.1 ((e y).2 0) hy.2
    rw [cylinder_coordinates_inverse_left n y] at h
    exact h
  have hm := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hΩ
  have hpre : (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ⁻¹' Ω = S ×ˢ Ioo a b := by
    ext p
    simp only [Ω, mem_preimage, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply,
      PiLp.single_apply, ↓reduceIte, mem_prod]
  rw [hpre, ← Measure.prod_restrict] at hm
  have hμmono : volume.restrict Ω ≤ volume.restrict (ball z R) :=
    Measure.restrict_mono_set volume hΩsub
  obtain ⟨m, hmSmooth, hmW, hmConv, hmDConv⟩ := hu.smoothDensity_memW12_ball hR
  let f : Bool → ℕ → Domain (n + 1) → Ambient q := fun b k =>
    if b then (fun y => coordinateDerivative (m k) (hmSmooth k) j y) else m k
  let v : Bool → Domain (n + 1) → Ambient q := fun b =>
    if b then (fun y => Du y j) else u
  have hf (b : Bool) (k : ℕ) : MemLp (f b k) 2 (volume.restrict (ball z R)) := by
    cases b
    · exact (hmW k).2.1
    · exact (hmW k).2.2 j
  have hv (b : Bool) : MemLp (v b) 2 (volume.restrict (ball z R)) := by
    cases b
    · exact hu.2.1
    · exact hu.2.2 j
  have hconv (b : Bool) : Tendsto (fun k => eLpNorm (f b k - v b) 2
      (volume.restrict (ball z R))) atTop (𝓝 0) := by
    cases b
    · exact hmConv
    · exact hmDConv j
  let F : Bool → ℕ → Domain n × ℝ → Ambient q := fun b k p =>
    f b k (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  let V : Bool → Domain n × ℝ → Ambient q := fun b p =>
    v b (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  have hF (b : Bool) (k : ℕ) : MemLp (F b k) 2 (μ.prod ν) :=
    ((hf b k).mono_measure hμmono).comp_measurePreserving hm
  have hV (b : Bool) : MemLp (V b) 2 (μ.prod ν) :=
    ((hv b).mono_measure hμmono).comp_measurePreserving hm
  have hFconv (b : Bool) : Tendsto (fun k => eLpNorm (F b k - V b) 2 (μ.prod ν))
      atTop (𝓝 0) := by
    have heq (k : ℕ) : eLpNorm (F b k - V b) 2 (μ.prod ν) =
        eLpNorm (f b k - v b) 2 (volume.restrict Ω) :=
      eLpNorm_comp_measurePreserving
        (((hf b k).sub (hv b)).mono_measure hμmono).aestronglyMeasurable hm
    simp_rw [heq]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv b)
      (fun _ => zero_le) (fun k => eLpNorm_mono_measure _ hμmono)
  obtain ⟨κ, hκ, hae⟩ := exists_subseq_ae_tendsto_prod_l2_family hF hV hFconv
  filter_upwards [hae] with x hx
  have hmLine (k : ℕ) : ContDiff ℝ ∞
      (fun t => m (κ k) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
    dsimp only [e]
    simp_rw [coordinateLine_affine]
    exact (hmSmooth (κ k)).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hderivLine (k : ℕ) (t : ℝ) : HasDerivAt
      (fun t => m (κ k) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
      (coordinateDerivative (m (κ k)) (hmSmooth (κ k)) j
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) t := by
    have hL : HasDerivAt (fun t : ℝ =>
        e.symm (x, 0) + t • EuclideanSpace.single j (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add (e.symm (x, 0))
    have hd := ((hmSmooth (κ k)).differentiable (by simp)
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))).hasFDerivAt
    dsimp only [e] at hd
    rw [coordinateLine_affine] at hd
    have H := hd.comp_hasDerivAt t hL
    simpa only [Function.comp_def, e, j, ← coordinateLine_affine, coordinateDerivative] using H
  have hweak := interval_weakDerivative_of_L2_convergence
    (hf := fun k => (hx false).1 (κ k))
    (hg := fun k => (hx true).1 (κ k))
    (hu := (hx false).2.1) (hv := (hx true).2.1)
    (hx false).2.2 (hx true).2.2 (fun k φ hφ hcφ hsφ => by
      apply smooth_curve_weakDerivative hab (hmLine k)
        (g := fun t => coordinateDerivative (m (κ k)) (hmSmooth (κ k)) j
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
      · dsimp only [e]
        simp_rw [coordinateLine_affine]
        exact (((hmSmooth (κ k)).continuous_fderiv (by simp)).clm_apply continuous_const).comp
          (continuous_const.add (continuous_id.smul continuous_const))
      · exact hderivLine k
      · exact hφ
      · exact hcφ
      · exact hsφ)
  refine ⟨(hx false).2.1, (hx true).2.1, ?_⟩
  apply interval_weakDerivative_exists_ac_representative hab
    (hf := (hx false).2.1) (hg := (hx true).2.1)
  intro φ hφ hcφ hsφ
  have hid := hweak φ hφ hcφ hsφ
  have hrestriction (ψ : ℝ → ℝ) (hs : tsupport ψ ⊆ Ioo a b) (W : ℝ → Ambient q) :
      (∫ t in Ioo a b, ψ t • W t) = ∫ t, ψ t • W t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun hm => ht (hs hm)), zero_smul]
  rw [hrestriction (deriv φ) (tsupport_deriv_subset.trans hsφ), hrestriction φ hsφ]
  exact hid

end StratificationTheory
