module

public import StratificationTheory.Foundation.RadialProductL2
public import HarmonicMaps.Sobolev
import HarmonicMaps.Analysis.SobolevSmoothDensity
import HarmonicMaps.Analysis.VariableMollificationL2
import StratificationTheory.Foundation.PolarSliceConvergence
import StratificationTheory.Foundation.IntervalWeakDerivativeClosure
import HolderToCK.Analysis.Bootstrap.AffineMinimizer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual ambient radial weak identities

Smooth ambient graph approximation converges on the native sphere-radius
product. A common sequence of ray restrictions retains both the original map
and its original radial weak columns. Their distributional identity follows
from smooth integration by parts and L2 closure on each ray.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators ContDiff
namespace StratificationTheory

private theorem exists_subseq_ae_ray_L2 {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [SigmaFinite μ] {a b : ℝ}
    {f : ℕ → α × ℝ → E} {u : α × ℝ → E}
    (hf : ∀ k, MemLp (f k) 2 (μ.prod (volume.restrict (Icc a b))))
    (hu : MemLp u 2 (μ.prod (volume.restrict (Icc a b))))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2
      (μ.prod (volume.restrict (Icc a b)))) atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ θ ∂μ,
        (∀ k, MemLp (fun r => f k (θ, r)) 2 (volume.restrict (Icc a b))) ∧
        MemLp (fun r => u (θ, r)) 2 (volume.restrict (Icc a b)) ∧
        Tendsto (fun k => eLpNorm (fun r => f (κ k) (θ, r) - u (θ, r)) 2
          (volume.restrict (Icc a b))) atTop (𝓝 0) := by
  let ν := volume.restrict (Icc a b)
  have herr (k : ℕ) : MemLp (f k - u) 2 (μ.prod ν) := (hf k).sub hu
  have hsq := tendsto_integral_norm_sq_zero_of_eLpNorm_two herr hconv
  let F : ℕ → ℝ × α → ℝ := fun k p => ‖f k (p.2, p.1) - u (p.2, p.1)‖ ^ 2
  have hF (k : ℕ) : Integrable (F k) (ν.prod μ) :=
    (Measure.measurePreserving_swap.integrable_comp_emb
      MeasurableEquiv.prodComm.measurableEmbedding).mpr
        ((herr k).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hFlim : Tendsto (fun k => ∫ p, F k p ∂ν.prod μ) atTop (𝓝 0) := by
    have heq (k : ℕ) : (∫ p, F k p ∂ν.prod μ) =
        ∫ p, ‖(f k - u) p‖ ^ 2 ∂μ.prod ν := by
      exact Measure.measurePreserving_swap.integral_comp
        MeasurableEquiv.prodComm.measurableEmbedding
        (fun p : α × ℝ => ‖(f k - u) p‖ ^ 2)
    simpa only [heq] using hsq
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_tendsto_integral_slice_zero hF
    (fun _ _ => sq_nonneg _) hFlim
  have hfRay : ∀ᵐ θ ∂μ, ∀ k,
      MemLp (fun r => f k (θ, r)) 2 ν := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [(hf k).aestronglyMeasurable.prodMk_left,
      ((hf k).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).prod_right_ae] with θ hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have huRay : ∀ᵐ θ ∂μ, MemLp (fun r => u (θ, r)) 2 ν := by
    filter_upwards [hu.aestronglyMeasurable.prodMk_left,
      (hu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).prod_right_ae] with θ hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hi
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hκae, hfRay, huRay] with θ hθ hfθ huθ
  exact ⟨hfθ, huθ, tendsto_eLpNorm_two_zero_of_integral_norm_sq
    (fun k => (hfθ (κ k)).sub huθ) hθ.2⟩

private theorem smooth_ray_hasDerivAt {n q : ℕ} {f : Domain n → Ambient q}
    (hf : ContDiff ℝ ∞ f) (c θ : Domain n) (r : ℝ) :
    HasDerivAt (fun t => f (c + t • θ))
      (∑ i : Fin n, θ i • coordinateDerivative f hf i (c + r • θ)) r := by
  have hlin : HasDerivAt (fun t : ℝ => c + t • θ) θ r :=
    by
      convert (hasDerivAt_const r c).add ((hasDerivAt_id r).smul_const θ) using 1 <;>
        first | rfl | simp only [zero_add, one_smul]
  have h := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt r hlin
  have hrepr : (∑ i : Fin n, θ i • EuclideanSpace.single i 1) = θ := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr θ
  apply h.congr_deriv
  calc
    _ = fderiv ℝ f (c + r • θ) (∑ i : Fin n, θ i • EuclideanSpace.single i 1) :=
      congrArg (fderiv ℝ f (c + r • θ)) hrepr.symm
    _ = _ := by simp only [map_sum, map_smul, coordinateDerivative]

private theorem smooth_ray_weak_identity {n q : ℕ} {f : Domain n → Ambient q}
    (hf : ContDiff ℝ ∞ f) (c θ : Domain n) {a b : ℝ} (hab : a < b)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (_hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ r, deriv φ r • f (c + r • θ)) =
      -(∫ r, φ r • ∑ i : Fin n, θ i • coordinateDerivative f hf i (c + r • θ)) := by
  let F : ℝ → Ambient q := fun r => f (c + r • θ)
  let G : ℝ → Ambient q := fun r => ∑ i : Fin n, θ i • coordinateDerivative f hf i (c + r • θ)
  have harg : Continuous (fun r : ℝ => c + r • θ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hFC : Continuous F := hf.continuous.comp harg
  have hGC : Continuous G := by
    apply continuous_finsetSum Finset.univ
    intro i _
    change Continuous (fun r : ℝ => θ i • fderiv ℝ f (c + r • θ) (EuclideanSpace.single i 1))
    have hDx : Continuous (fun r : ℝ => fderiv ℝ f (c + r • θ)) :=
      (hf.continuous_fderiv (by simp)).comp harg
    exact (continuous_const (y := θ i)).smul (hDx.clm_apply
      (continuous_const (y := EuclideanSpace.single i (1 : ℝ))))
  have hφD : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := φ) (v := F) (u' := deriv φ) (v' := G)
    (fun r _ => (hφ.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun r _ => smooth_ray_hasDerivAt hf c θ r)
    (hφD.intervalIntegrable a b) (hGC.intervalIntegrable a b)
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl a) (hsφ h).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl b) (hsφ h).2)
  have hrestrict (ψ : ℝ → ℝ) (hψ : tsupport ψ ⊆ Ioo a b) (V : ℝ → Ambient q) :
      (∫ r in a..b, ψ r • V r) = ∫ r, ψ r • V r := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun h => hr (hψ h)), zero_smul]
  rw [hφa, hφb, zero_smul, zero_smul, sub_self, zero_sub] at hparts
  rw [hrestrict φ hsφ G, hrestrict (deriv φ) (tsupport_deriv_subset.trans hsφ) F] at hparts
  simpa only [neg_neg] using (congrArg Neg.neg hparts).symm


private theorem normalized_radial_columns_polar_eq {n q : ℕ}
    (D : Domain n → Gradient n q) (c : Domain n)
    (θ : sphere (0 : Domain n) 1) {r : ℝ} (hr : 0 < r) :
    (‖c + r • θ.val - c‖⁻¹ •
      ∑ i : Fin n, (c + r • θ.val - c) i • D (c + r • θ.val) i) =
      ∑ i : Fin n, θ.val i • D (c + r • θ.val) i := by
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le, hθ, mul_one, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  have hcoeff : r⁻¹ * (r • θ.val) i = θ.val i := by
    change r⁻¹ * (r * θ.val i) = θ.val i
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  rw [hcoeff]

/-- Actual full Sobolev data give the native radial product L2 map and its
original radial weak columns, with every time test identity derived from
smooth graph approximation. -/
theorem radial_product_weak_identity_of_memW12_ball {n q : ℕ} (hn : 0 < n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    {c : Domain n} {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R)
    (hu : MemW12 (ballDomain c R) u Du) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let F : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p => u (c + p.2 • p.1.val)
    let G : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p =>
      ∑ i : Fin n, p.1.val i • Du (c + p.2 • p.1.val) i
    MemLp F 2 (σ.prod (volume.restrict (Icc a b))) ∧
    MemLp G 2 (σ.prod (volume.restrict (Icc a b))) ∧
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ θ ∂σ, (∫ r in Icc a b, deriv φ r • F (θ, r)) =
        -(∫ r in Icc a b, φ r • G (θ, r)) := by
  intro σ F G
  let ν := volume.restrict (Icc a b)
  let μ := σ.prod ν
  letI : IsFiniteMeasure σ := by
    dsimp [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hR : 0 < R := (ha.trans hab).trans hbR
  obtain ⟨m, hm, hmW, hmconv, hDconv⟩ := hu.smoothDensity_memW12_ball hR
  let D : ℕ → Domain n → Gradient n q := fun k x i => coordinateDerivative (m k) (hm k) i x
  let f : ℕ → sphere (0 : Domain n) 1 × ℝ → Ambient q := fun k p => m k (c + p.2 • p.1.val)
  let g : ℕ → sphere (0 : Domain n) 1 × ℝ → Ambient q := fun k p =>
    ∑ i : Fin n, p.1.val i • D k (c + p.2 • p.1.val) i
  let N : (Domain n → Gradient n q) → Domain n → Ambient q := fun V x =>
    ‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • V x i
  have hN (V : Domain n → Gradient n q)
      (hV : ∀ i, MemLp (fun x => V x i) 2 (volume.restrict (ball c R))) :
      MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
        ∑ i : Fin n, p.1.val i • V (c + p.2 • p.1.val) i) 2 μ := by
    have hVN := memLp_two_radial_product_ball hn ha hbR
      (memLp_two_normalized_radial_columns hV c)
    apply hVN.ae_eq
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (measurableSet_Icc (a := a) (b := b)))] with p hp
    exact normalized_radial_columns_polar_eq V c p.1 (ha.trans_le hp.1)
  have hf (k : ℕ) : MemLp (f k) 2 μ :=
    memLp_two_radial_product_ball hn ha hbR (hmW k).2.1
  have hF : MemLp F 2 μ := memLp_two_radial_product_ball hn ha hbR hu.2.1
  have hg (k : ℕ) : MemLp (g k) 2 μ := hN (D k) (hmW k).2.2
  have hG : MemLp G 2 μ := hN Du hu.2.2
  have hfconv : Tendsto (fun k => eLpNorm (f k - F) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_radial_product_sub hn ha hbR (fun k => (hmW k).2.1) hu.2.1 hmconv
  have hNconv := tendsto_eLpNorm_two_normalized_radial_columns_sub
    (fun k => (hmW k).2.2) hu.2.2 hDconv c
  have hGNconv := tendsto_eLpNorm_two_radial_product_sub hn ha hbR
    (fun k => memLp_two_normalized_radial_columns (hmW k).2.2 c)
    (memLp_two_normalized_radial_columns hu.2.2 c) hNconv
  have hgconv : Tendsto (fun k => eLpNorm (g k - G) 2 μ) atTop (𝓝 0) := by
    have heq (k : ℕ) : eLpNorm (g k - G) 2 μ =
        eLpNorm (fun p : sphere (0 : Domain n) 1 × ℝ =>
          N (D k) (c + p.2 • p.1.val) - N Du (c + p.2 • p.1.val)) 2 μ := by
      apply eLpNorm_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (measurableSet_Icc (a := a) (b := b)))] with p hp
      dsimp only [Pi.sub_apply, g, G, N]
      rw [normalized_radial_columns_polar_eq (D k) c p.1 (ha.trans_le hp.1),
        normalized_radial_columns_polar_eq Du c p.1 (ha.trans_le hp.1)]
    simpa only [heq] using hGNconv
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_ray_L2 hf hF hfconv
  obtain ⟨η, hη, hηae⟩ := exists_subseq_ae_ray_L2 (fun k => hg (κ k)) hG
    (hgconv.comp hκ.tendsto_atTop)
  have hνmono : volume.restrict (Ioo a b) ≤ ν :=
    Measure.restrict_mono_set volume Ioo_subset_Icc_self
  have hweak : ∀ᵐ θ ∂σ, ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ r, deriv φ r • F (θ, r)) = -(∫ r, φ r • G (θ, r)) := by
    filter_upwards [hκae, hηae] with θ hθ hθ'
    apply interval_weakDerivative_of_L2_convergence
      (fun k => (hθ.1 (κ (η k))).mono_measure hνmono)
      (fun k => (hθ'.1 (η k)).mono_measure hνmono)
      (hθ.2.1.mono_measure hνmono) (hθ'.2.1.mono_measure hνmono)
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hθ.2.2.comp hη.tendsto_atTop) (fun _ => zero_le)
      exact fun _ => eLpNorm_mono_measure _ hνmono
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hθ'.2.2 (fun _ => zero_le)
      exact fun _ => eLpNorm_mono_measure _ hνmono
    · intro k φ hφ hcφ hsφ
      exact smooth_ray_weak_identity (hm (κ (η k))) c θ.val hab φ hφ hcφ hsφ
  refine ⟨hF, hG, ?_⟩
  intro φ hφ hcφ hsφ
  filter_upwards [hweak] with θ hθ
  have hrestrict (ψ : ℝ → ℝ) (hψ : tsupport ψ ⊆ Ioo a b) (V : ℝ → Ambient q) :
      (∫ r in Icc a b, ψ r • V r) = ∫ r, ψ r • V r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun h => hr (Ioo_subset_Icc_self (hψ h))), zero_smul]
  rw [hrestrict (deriv φ) (tsupport_deriv_subset.trans hsφ), hrestrict φ hsφ]
  exact hθ φ hφ hcφ hsφ

end StratificationTheory
