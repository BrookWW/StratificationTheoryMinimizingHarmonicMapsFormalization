module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.Basic
import StratificationTheory.Foundation.CubicalConeL2Fields
import StratificationTheory.Foundation.CubicalConeBochner
import StratificationTheory.Foundation.CubicalConeTimeParts
import StratificationTheory.Foundation.IntervalSobolevProductSpatialTrace
import HarmonicMaps.Analysis.SobolevCutoff

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators ContDiff
open StratificationTheory
namespace StratificationTheory.Providers.CubicalFaceConeExtensionV2

private theorem cone_test_pair_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {d q : ℕ}
    {f : X → Ambient q} (hf : MemLp f 2 μ)
    {c : X → ℝ} (hc : MemLp c ∞ μ)
    (P : X × ℝ → Domain d) (hP : Measurable P)
    {φ : Domain d → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (m : ℕ) :
    Integrable (fun p : X × ℝ => (p.2 ^ m * c p.1 * φ (P p)) • f p.1)
      (μ.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  let ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have hweight : MemLp (fun t : ℝ => t ^ m) ∞ ν := by
    have hcont : Continuous (fun t : ℝ => t ^ m) := continuous_id.pow m
    apply memLp_top_of_bound hcont.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le m)]
    exact pow_le_one₀ ht.1.le ht.2.le
  have htest : MemLp φ ∞ (Measure.map P (μ.prod ν)) :=
    hφ.memLp_top_of_hasCompactSupport hcφ _
  have htestP : MemLp (φ ∘ P) ∞ (μ.prod ν) := htest.comp_of_map hP.aemeasurable
  have hcoef' : MemLp (fun p : X × ℝ => φ (P p) * (c p.1 * p.2 ^ m)) ∞ (μ.prod ν) :=
    ((hweight.comp_snd μ).mul (r := ∞) (hc.comp_fst ν)).mul (r := ∞) htestP
  have hcoef : MemLp (fun p : X × ℝ => p.2 ^ m * c p.1 * φ (P p)) ∞ (μ.prod ν) :=
    hcoef'.ae_eq (Eventually.of_forall fun _ => by ring)
  have hfield : MemLp (fun p : X × ℝ => (p.2 ^ m * c p.1 * φ (P p)) • f p.1) 2 (μ.prod ν) :=
    (hf.comp_fst ν).smul (r := (2 : ℝ≥0∞)) hcoef
  exact hfield.integrable (by norm_num)

private theorem cone_spatial_weak {n q : ℕ} {B : OpenDomain n}
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasWeakGradient B w Dw) (C : OpenDomain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    C.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} →
    IntegrableOn (fun y => w (ξ y)) C.val volume →
    (∀ i, IntegrableOn (fun y => (T y)⁻¹ • Dw (ξ y) i) C.val volume) →
    ∀ (i : Fin n) (φ : Domain (n + 1) → ℝ) (hφ : ContDiff ℝ ∞ φ),
      HasCompactSupport φ → tsupport φ ⊆ C.val →
      (∫ y in C.val, coordinateDerivative φ hφ (Fin.castAdd 1 i) y • w (ξ y)) =
        -(∫ y in C.val, φ y • ((T y)⁻¹ • Dw (ξ y) i)) := by
  intro e T ξ hC hW hDw i φ hφ hcφ hsφ
  let P : Domain n → ℝ → Domain (n + 1) := fun x t =>
    e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)
  have hT (x : Domain n) (t : ℝ) : T (P x t) = t := by
    dsimp only [T, P]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
  have hξ (x : Domain n) (t : ℝ) (ht : t ≠ 0) : ξ (P x t) = x := by
    dsimp only [ξ, P]
    rw [hT, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hφTop : MemLp φ ∞ (volume.restrict C.val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hφiTop : MemLp (coordinateDerivative φ hφ (Fin.castAdd 1 i)) ∞
      (volume.restrict C.val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single (Fin.castAdd 1 i) 1)) _
  have hLI := hW.smul_of_top_right hφiTop
  have hRI := (hDw i).smul_of_top_right hφTop
  have hLI' : IntegrableOn
      (fun y => coordinateDerivative φ hφ (Fin.castAdd 1 i) y • w (ξ y))
      {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} volume := by
    rw [← hC]
    exact hLI
  have hRI' : IntegrableOn (fun y => φ y • ((T y)⁻¹ • Dw (ξ y) i))
      {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} volume := by
    rw [← hC]
    exact hRI
  have hL := integral_native_positive_cone B.property.measurableSet
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1) hLI'
  have hR := integral_native_positive_cone B.property.measurableSet
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1) hRI'
  have hsp (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (∫ x in B.val, coordinateDerivative φ hφ (Fin.castAdd 1 i) (P x t) • w x) =
        -(t⁻¹ • ∫ x in B.val, φ (P x t) • Dw x i) := by
    let ψ : Domain n → ℝ := fun x => φ (P x t)
    have hψ : ContDiff ℝ ∞ ψ := hφ.comp (e.symm.contDiff.comp
      ((contDiff_const_smul t).prodMk contDiff_const))
    have hcψ : HasCompactSupport ψ := hasCompactSupport_cone_test_spatial hcφ ht.1.ne'
    have hsψ : tsupport ψ ⊆ B.val :=
      tsupport_cone_test_subset_face ht.1.ne' (fun y hy => (hC ▸ hsφ hy).2)
    have hderiv (x : Domain n) : coordinateDerivative ψ hψ i x =
        t * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P x t) :=
      coordinateDerivative_cone_test_spatial hφ t x i
    have hweak := hw.2.2 i ψ hψ hcψ hsψ
    simp_rw [hderiv, mul_smul] at hweak
    rw [integral_smul] at hweak
    calc
      _ = t⁻¹ • (t • ∫ x in B.val, coordinateDerivative φ hφ (Fin.castAdd 1 i) (P x t) • w x) := by
        rw [smul_smul, inv_mul_cancel₀ ht.1.ne', one_smul]
      _ = _ := by rw [hweak, smul_neg]
  rw [hC]
  rw [hL, hR, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change t ^ n • (∫ x in B.val, coordinateDerivative φ hφ (Fin.castAdd 1 i) (P x t) • w (ξ (P x t))) =
    -(t ^ n • ∫ x in B.val, φ (P x t) • ((T (P x t))⁻¹ • Dw (ξ (P x t)) i))
  simp_rw [hT, hξ _ _ ht.1.ne']
  rw [hsp t ht]
  simp_rw [smul_comm (φ _) t⁻¹]
  rw [integral_smul, smul_neg]

private theorem cone_weighted_face_weak {n q : ℕ} {B : OpenDomain n}
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasWeakGradient B w Dw) {φ : Domain (n + 1) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let P : Domain n → ℝ → Domain (n + 1) := fun x t =>
      e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)
    tsupport φ ⊆ {y : Domain (n + 1) | ((e y).2 0)⁻¹ • (e y).1 ∈ B.val} →
    ∀ (t : ℝ), 0 < t → ∀ i : Fin n,
      (∫ x in B.val, (φ (P x t) + x i * (t * coordinateDerivative φ hφ
        (Fin.castAdd 1 i) (P x t))) • w x) =
        -(∫ x in B.val, (x i * φ (P x t)) • Dw x i) := by
  intro e P hs t ht i
  let ψ : Domain n → ℝ := fun x => φ (P x t)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (e.symm.contDiff.comp
    ((contDiff_const_smul t).prodMk contDiff_const))
  have hcψ : HasCompactSupport ψ := hasCompactSupport_cone_test_spatial hcφ ht.ne'
  have hsψ : tsupport ψ ⊆ B.val := tsupport_cone_test_subset_face ht.ne' hs
  have hψD (x : Domain n) : coordinateDerivative ψ hψ i x =
      t * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P x t) :=
    coordinateDerivative_cone_test_spatial hφ t x i
  let χ : Domain n → ℝ := fun x => x i * ψ x
  have hproj : ContDiff ℝ ∞ (fun x : Domain n => x i) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hχ : ContDiff ℝ ∞ χ := hproj.mul hψ
  have hcχ : HasCompactSupport χ := hcψ.mul_left
  have hsχ : tsupport χ ⊆ B.val := tsupport_mul_subset_right.trans hsψ
  have hprojD (x : Domain n) : coordinateDerivative (fun x : Domain n => x i) hproj i x = 1 := by
    have h : HasFDerivAt (fun x : Domain n => x i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    change fderiv ℝ (fun x : Domain n => x i) x (EuclideanSpace.single i 1) = 1
    rw [h.fderiv]
    change (EuclideanSpace.single i (1 : ℝ)) i = 1
    simp only [PiLp.single_apply, ite_true]
  have hχD (x : Domain n) : coordinateDerivative χ hχ i x =
      φ (P x t) + x i * (t * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P x t)) := by
    change coordinateDerivative (fun x : Domain n => x i * ψ x) (hproj.mul hψ) i x = _
    rw [coordinateDerivative_mul hproj hψ, hprojD, one_mul, hψD]
  have hweak := hw.2.2 i χ hχ hcχ hsχ
  simpa only [hχD, χ, ψ] using hweak

private theorem cone_time_row {n q : ℕ} (w : Domain n → Ambient q)
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let P : Domain n × ℝ → Domain (n + 1) := fun p =>
      e.symm (p.2 • p.1, EuclideanSpace.single (0 : Fin 1) p.2)
    tsupport φ ⊆ {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1} →
    ∀ x : Domain n,
      (∫ t in Ioo (0 : ℝ) 1,
        (t ^ n * coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P (x,t))) • w x +
        ∑ i : Fin n, (t ^ n * x i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x,t))) • w x) =
      -((n : ℝ) • ∫ t in Ioo (0 : ℝ) 1, (t ^ (n - 1) * φ (P (x,t))) • w x) := by
  intro e P hsTime x
  let ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  let A : Domain n × ℝ → Ambient q := fun p =>
    (p.2 ^ n * coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P p)) • w p.1
  let Bf : Fin n → Domain n × ℝ → Ambient q := fun i p =>
    (p.2 ^ n * p.1 i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P p)) • w p.1
  let Cf : Domain n × ℝ → Ambient q := fun p => (p.2 ^ (n - 1) * φ (P p)) • w p.1
  have hs := integral_cone_test_time_parts n hφ hsTime x
  have hv := congrArg (fun r : ℝ => r • w x) hs
  have hleft :
      ((∫ t in Ioo (0 : ℝ) 1, t ^ n *
        ((∑ i : Fin n, x i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x, t))) +
          coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P (x, t)))) • w x) =
        ∫ t, A (x, t) + ∑ i : Fin n, Bf i (x, t) ∂ν := by
    rw [← integral_smul_const]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    dsimp only [A, Bf]
    simp only [mul_add, add_smul, Finset.mul_sum, Finset.sum_smul, mul_assoc]
    exact add_comm _ _
  have hright :
      (-((n : ℝ) * ∫ t in Ioo (0 : ℝ) 1, t ^ (n - 1) * φ (P (x, t)))) • w x =
        -((n : ℝ) • ∫ t, Cf (x, t) ∂ν) := by
    rw [neg_smul, mul_smul, ← integral_smul_const]
  exact hleft.symm.trans (hv.trans hright)


private theorem cone_space_row {n q : ℕ} (hn : 1 ≤ n) {B : OpenDomain n}
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasWeakGradient B w Dw) {φ : Domain (n + 1) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let P : Domain n × ℝ → Domain (n + 1) := fun p =>
      e.symm (p.2 • p.1, EuclideanSpace.single (0 : Fin 1) p.2)
    tsupport φ ⊆ {y : Domain (n + 1) | ((e y).2 0)⁻¹ • (e y).1 ∈ B.val} →
    ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      (∫ x in B.val,
        (t ^ n * x i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x,t))) • w x +
        (t ^ (n - 1) * φ (P (x,t))) • w x) =
      -(∫ x in B.val, (t ^ (n - 1) * x i * φ (P (x,t))) • Dw x i) := by
  intro e P hsInv t ht i
  let μ := (volume : Measure (Domain n)).restrict B.val
  let Bf : Fin n → Domain n × ℝ → Ambient q := fun i p =>
    (p.2 ^ n * p.1 i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P p)) • w p.1
  let Cf : Domain n × ℝ → Ambient q := fun p => (p.2 ^ (n - 1) * φ (P p)) • w p.1
  let Rf : Fin n → Domain n × ℝ → Ambient q := fun i p =>
    (p.2 ^ (n - 1) * p.1 i * φ (P p)) • Dw p.1 i
  have hs := cone_weighted_face_weak hw hφ hcφ hsInv t ht i
  have hv := congrArg (fun v : Ambient q => t ^ (n - 1) • v) hs
  have hpow : t ^ (n - 1) * t = t ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hleft :
      t ^ (n - 1) • (∫ x in B.val, (φ (P (x, t)) +
        x i * (t * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x, t)))) • w x) =
        ∫ x, Bf i (x, t) + Cf (x, t) ∂μ := by
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only [Bf, Cf]
    rw [smul_smul, mul_add, add_smul]
    have hcoef : t ^ (n - 1) * (x i * (t * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x, t)))) =
        t ^ n * x i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x, t)) := by
      calc
        _ = (t ^ (n - 1) * t) * x i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P (x, t)) := by ring
        _ = _ := by rw [hpow]
    rw [hcoef]
    exact add_comm _ _
  have hright :
      t ^ (n - 1) • (-(∫ x in B.val, (x i * φ (P (x, t))) • Dw x i)) =
        -(∫ x, Rf i (x, t) ∂μ) := by
    rw [smul_neg, ← integral_smul]
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only [Rf]
    rw [smul_smul]
    congr 1
    ring
  exact hleft.symm.trans (hv.trans hright)


private theorem cone_product_cancel {X : Type*} [MeasurableSpace X] {n q : ℕ}
    (μ : Measure X) (ν : Measure ℝ) [SFinite μ] [SFinite ν] (hν : ∀ᵐ t ∂ν, 0 < t)
    (A Cf : X × ℝ → Ambient q) (Bf Rf : Fin n → X × ℝ → Ambient q)
    (hAI : Integrable A (μ.prod ν)) (hCI : Integrable Cf (μ.prod ν))
    (hBI : ∀ i, Integrable (Bf i) (μ.prod ν))
    (hRI : ∀ i, Integrable (Rf i) (μ.prod ν))
    (hTimeRow : ∀ x, (∫ t, A (x,t) + ∑ i, Bf i (x,t) ∂ν) =
      -((n : ℝ) • ∫ t, Cf (x,t) ∂ν))
    (hSpaceRow : ∀ t, 0 < t → ∀ i, (∫ x, Bf i (x,t) + Cf (x,t) ∂μ) =
      -(∫ x, Rf i (x,t) ∂μ)) :
    (∫ p, A p ∂μ.prod ν) = ∫ p, ∑ i, Rf i p ∂μ.prod ν := by
  let R : X × ℝ → Ambient q := fun p => ∑ i, Rf i p
  have hBsumI : Integrable (fun p => ∑ i : Fin n, Bf i p) (μ.prod ν) :=
    integrable_finsetSum Finset.univ (fun i _ => hBI i)
  have hTimeGlobal : (∫ p, A p ∂μ.prod ν) +
      (∑ i : Fin n, ∫ p, Bf i p ∂μ.prod ν) =
        -((n : ℝ) • ∫ p, Cf p ∂μ.prod ν) := by
    have hABI : Integrable (fun p => A p + ∑ i : Fin n, Bf i p) (μ.prod ν) := hAI.fun_add hBsumI
    calc
      _ = ∫ p, A p + ∑ i : Fin n, Bf i p ∂μ.prod ν := by
        rw [integral_add hAI hBsumI, integral_finsetSum Finset.univ (fun i _ => hBI i)]
      _ = ∫ x, (∫ t, A (x, t) + ∑ i : Fin n, Bf i (x, t) ∂ν) ∂μ := integral_prod _ hABI
      _ = ∫ x, -((n : ℝ) • ∫ t, Cf (x, t) ∂ν) ∂μ := by simp_rw [hTimeRow]
      _ = _ := by rw [integral_neg, integral_smul, ← integral_prod _ hCI]
  have hSpaceGlobal (i : Fin n) :
      (∫ p, Bf i p ∂μ.prod ν) + (∫ p, Cf p ∂μ.prod ν) = -(∫ p, Rf i p ∂μ.prod ν) := by
    have hBCI : Integrable (fun p => Bf i p + Cf p) (μ.prod ν) := (hBI i).fun_add hCI
    calc
      _ = ∫ p, Bf i p + Cf p ∂μ.prod ν := (integral_add (hBI i) hCI).symm
      _ = ∫ t, (∫ x, Bf i (x, t) + Cf (x, t) ∂μ) ∂ν := integral_prod_symm _ hBCI
      _ = ∫ t, -(∫ x, Rf i (x, t) ∂μ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hν] with t ht
        exact hSpaceRow t ht i
      _ = _ := by rw [integral_neg, ← integral_prod_symm _ (hRI i)]
  have hSpaceSum : (∑ i : Fin n, ∫ p, Bf i p ∂μ.prod ν) +
      (n : ℝ) • (∫ p, Cf p ∂μ.prod ν) = -(∫ p, R p ∂μ.prod ν) := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hSpaceGlobal i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_neg_distrib, ← Nat.cast_smul_eq_nsmul ℝ] at hs
    have hRIntegral : (∫ p, R p ∂μ.prod ν) = ∑ i : Fin n, ∫ p, Rf i p ∂μ.prod ν :=
      integral_finsetSum Finset.univ (fun i _ => hRI i)
    rwa [← hRIntegral] at hs
  have ha := eq_sub_of_add_eq hTimeGlobal
  have hb := eq_sub_of_add_eq hSpaceSum
  rw [hb] at ha
  calc
    _ = _ := ha
    _ = _ := by abel


private theorem cone_time_product {n q : ℕ} (hn : 1 ≤ n) (B : OpenDomain n)
    (hBfinite : (volume : Measure (Domain n)) B.val ≠ ⊤)
    (hcoordB : ∀ x ∈ B.val, ∀ i : Fin n, |x i| ≤ 1)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12 B w Dw) {φ : Domain (n + 1) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let P : Domain n × ℝ → Domain (n + 1) := fun p =>
      e.symm (p.2 • p.1, EuclideanSpace.single (0 : Fin 1) p.2)
    tsupport φ ⊆ {y : Domain (n + 1) | ((e y).2 0)⁻¹ • (e y).1 ∈ B.val} →
    tsupport φ ⊆ {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1} →
    let μ := (volume : Measure (Domain n)).restrict B.val
    let ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
    let A : Domain n × ℝ → Ambient q := fun p =>
      (p.2 ^ n * coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P p)) • w p.1
    let R : Domain n × ℝ → Ambient q := fun p =>
      (p.2 ^ (n - 1) * φ (P p)) • ∑ i : Fin n, p.1 i • Dw p.1 i
    Integrable A (μ.prod ν) ∧ Integrable R (μ.prod ν) ∧
      (∫ p, A p ∂μ.prod ν) = ∫ p, R p ∂μ.prod ν := by
  intro e P hsInv hsTime μ ν A R
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hBfinite
  have hInv : Measurable (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) :=
    (measurePreserving_cylinder_coordinates_inverse n).measurable
  have hScale : Measurable (fun p : Domain n × ℝ => (p.2 • p.1, p.2)) :=
    (measurable_snd.smul measurable_fst).prodMk measurable_snd
  have hP : Measurable P := by
    change Measurable ((fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ∘
      (fun p : Domain n × ℝ => (p.2 • p.1, p.2)))
    exact hInv.comp hScale
  have hc (i : Fin n) : MemLp (fun x : Domain n => x i) ∞ μ := by
    apply memLp_top_of_bound (f := fun x : Domain n => x i)
      (EuclideanSpace.proj i).continuous.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem B.property.measurableSet] with x hx
    simpa only [Real.norm_eq_abs] using hcoordB x hx i
  have hc1 : MemLp (fun _ : Domain n => (1 : ℝ)) ∞ μ := memLp_const 1
  let Bf : Fin n → Domain n × ℝ → Ambient q := fun i p =>
    (p.2 ^ n * p.1 i * coordinateDerivative φ hφ (Fin.castAdd 1 i) (P p)) • w p.1
  let Cf : Domain n × ℝ → Ambient q := fun p => (p.2 ^ (n - 1) * φ (P p)) • w p.1
  let Rf : Fin n → Domain n × ℝ → Ambient q := fun i p =>
    (p.2 ^ (n - 1) * p.1 i * φ (P p)) • Dw p.1 i
  have hφj (j : Fin (n + 1)) : Continuous (coordinateDerivative φ hφ j) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcφj (j : Fin (n + 1)) : HasCompactSupport (coordinateDerivative φ hφ j) :=
    hcφ.fderiv_apply ℝ (EuclideanSpace.single j 1)
  have hAI : Integrable A (μ.prod ν) := by
    simpa only [A, mul_one] using cone_test_pair_integrable μ hw.2.1 hc1 P hP
      (hφj (Fin.natAdd n (0 : Fin 1))) (hcφj _) n
  have hBI (i : Fin n) : Integrable (Bf i) (μ.prod ν) :=
    cone_test_pair_integrable μ hw.2.1 (hc i) P hP (hφj (Fin.castAdd 1 i)) (hcφj _) n
  have hCI : Integrable Cf (μ.prod ν) := by
    simpa only [Cf, mul_one] using cone_test_pair_integrable μ hw.2.1 hc1 P hP
      hφ.continuous hcφ (n - 1)
  have hRI (i : Fin n) : Integrable (Rf i) (μ.prod ν) :=
    cone_test_pair_integrable μ (hw.2.2 i) (hc i) P hP hφ.continuous hcφ (n - 1)
  have hBsumI : Integrable (fun p => ∑ i : Fin n, Bf i p) (μ.prod ν) :=
    integrable_finsetSum Finset.univ (fun i _ => hBI i)
  have hRsum : R = fun p => ∑ i : Fin n, Rf i p := by
    funext p
    dsimp only [R, Rf]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  have hRInt : Integrable R (μ.prod ν) := by
    rw [hRsum]
    exact integrable_finsetSum Finset.univ (fun i _ => hRI i)
  have hTimeRow (x : Domain n) :
      (∫ t, A (x, t) + ∑ i : Fin n, Bf i (x, t) ∂ν) =
        -((n : ℝ) • ∫ t, Cf (x, t) ∂ν) := cone_time_row w hφ hsTime x
  have hSpaceRow (t : ℝ) (ht : 0 < t) (i : Fin n) :
      (∫ x, Bf i (x, t) + Cf (x, t) ∂μ) = -(∫ x, Rf i (x, t) ∂μ) :=
    cone_space_row hn hw.1 hφ hcφ hsInv t ht i
  refine ⟨hAI, hRInt, ?_⟩
  rw [hRsum]
  apply cone_product_cancel μ ν _ A Cf Bf Rf hAI hCI hBI hRI hTimeRow hSpaceRow
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact ht.1

private theorem cone_time_weak {n q : ℕ} (hn : 1 ≤ n) (B : OpenDomain n)
    (hBfinite : (volume : Measure (Domain n)) B.val ≠ ⊤)
    (hcoordB : ∀ x ∈ B.val, ∀ i : Fin n, |x i| ≤ 1)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12 B w Dw) (C : OpenDomain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    C.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} →
    IntegrableOn (fun y => w (ξ y)) C.val volume →
    IntegrableOn (fun y => -((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (ξ y) i)) C.val volume →
    ∀ (φ : Domain (n + 1) → ℝ) (hφ : ContDiff ℝ ∞ φ),
      HasCompactSupport φ → tsupport φ ⊆ C.val →
      (∫ y in C.val, coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) y • w (ξ y)) =
        -(∫ y in C.val, φ y • (-((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (ξ y) i))) := by
  intro e T ξ hC hW hD φ hφ hcφ hsφ
  let P : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.2 • p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  have hT (x : Domain n) (t : ℝ) : T (P (x,t)) = t := by
    dsimp only [T, P]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
  have hξ (x : Domain n) (t : ℝ) (ht : t ≠ 0) : ξ (P (x,t)) = x := by
    dsimp only [ξ, P]
    rw [hT, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hsInv : tsupport φ ⊆ {y : Domain (n + 1) | ((e y).2 0)⁻¹ • (e y).1 ∈ B.val} :=
    fun y hy => (hC ▸ hsφ hy).2
  have hsTime : tsupport φ ⊆ {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1} :=
    fun y hy => (hC ▸ hsφ hy).1
  have hProd := cone_time_product hn B hBfinite hcoordB hw hφ hcφ hsInv hsTime
  have hφTop : MemLp φ ∞ (volume.restrict C.val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hφtTop : MemLp (coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1))) ∞
      (volume.restrict C.val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)) _
  have hLI := hW.smul_of_top_right hφtTop
  have hRI := hD.smul_of_top_right hφTop
  have hLI' : IntegrableOn
      (fun y => coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) y • w (ξ y))
      {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} volume := by
    rw [← hC]
    exact hLI
  have hRI' : IntegrableOn (fun y => φ y •
      (-((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (ξ y) i)))
      {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} volume := by
    rw [← hC]
    exact hRI
  have hL := integral_native_positive_cone B.property.measurableSet
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1) hLI'
  have hR := integral_native_positive_cone B.property.measurableSet
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1) hRI'
  let μ := (volume : Measure (Domain n)).restrict B.val
  let ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  let A : Domain n × ℝ → Ambient q := fun p =>
    (p.2 ^ n * coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P p)) • w p.1
  let R : Domain n × ℝ → Ambient q := fun p =>
    (p.2 ^ (n - 1) * φ (P p)) • ∑ i : Fin n, p.1 i • Dw p.1 i
  have hLeft : (∫ y in C.val, coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) y • w (ξ y)) =
      ∫ p, A p ∂μ.prod ν := by
    rw [hC, hL, integral_prod_symm _ hProd.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change t ^ n • (∫ x in B.val, coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P (x,t)) • w (ξ (P (x,t)))) =
      ∫ x in B.val, (t ^ n * coordinateDerivative φ hφ (Fin.natAdd n (0 : Fin 1)) (P (x,t))) • w x
    simp_rw [hξ _ _ ht.1.ne']
    rw [← integral_smul]
    exact integral_congr_ae (Eventually.of_forall fun _ => smul_smul _ _ _)
  have hRight : -(∫ y in C.val, φ y •
      (-((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (ξ y) i))) =
      ∫ p, R p ∂μ.prod ν := by
    rw [hC, hR, ← integral_neg, integral_prod_symm _ hProd.2.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change -(t ^ n • ∫ x in B.val, φ (P (x,t)) •
      (-((T (P (x,t)))⁻¹ • ∑ i : Fin n, (ξ (P (x,t))) i • Dw (ξ (P (x,t))) i))) =
      ∫ x in B.val, (t ^ (n - 1) * φ (P (x,t))) • ∑ i : Fin n, x i • Dw x i
    simp_rw [hT, hξ _ _ ht.1.ne']
    rw [← integral_smul, ← integral_neg]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    simp only [smul_neg, neg_neg, smul_smul]
    congr 1
    have hpow : t ^ (n - 1) * t = t ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [← hpow]
    field_simp [ht.1.ne']
  exact hLeft.trans (hProd.2.2.trans hRight.symm)

private theorem cone_memW12 {n q : ℕ} (hn : 2 ≤ n)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w Dw) :
    let _B : OpenDomain n :=
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let C : OpenDomain (n + 1) :=
      ⟨T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ i : Fin n, {y : Domain (n + 1) | |X y i| < T y},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_lt (((EuclideanSpace.proj i).continuous.comp
            (continuous_fst.comp e.continuous)).abs)
            ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous))))⟩
    let W : Domain (n + 1) → Ambient q := fun y => w (ξ y)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun i : Fin n => (T y)⁻¹ • Dw (ξ y) i)
        (fun _last : Fin 1 => -((T y)⁻¹ • (∑ i : Fin n, (ξ y) i • Dw (ξ y) i)))
    MemW12 C W D := by
  intro B e X T ξ C W D
  have hCset : C.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |X y i| < T y} := by
    ext y
    simp only [C, mem_inter_iff, mem_preimage, mem_iInter, mem_setOf_eq]
  have hCratio : C.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} := by
    rw [hCset]
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (X y)).mpr hy.2⟩
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (X y)).mp hy.2⟩
  have hData := native_unit_face_cone_l2_energy_data hn hw.2.1 hw.2.2
  have hMLW : MemLp W 2 (volume.restrict C.val) := by
    rw [hCset]
    exact hData.1
  have hMLD (i : Fin (n + 1)) : MemLp (fun y => D y i) 2 (volume.restrict C.val) := by
    rw [hCset]
    exact hData.2.1 i
  have hCfinite : (volume : Measure (Domain (n + 1))) C.val ≠ ⊤ := by
    rw [hCset]
    exact volume_native_unit_face_cone_ne_top n
  letI : IsFiniteMeasure ((volume : Measure (Domain (n + 1))).restrict C.val) :=
    isFiniteMeasure_restrict.mpr hCfinite
  have hWInt : IntegrableOn W C.val volume := hMLW.integrable (by norm_num)
  have hDInt (i : Fin (n + 1)) : IntegrableOn (fun y => D y i) C.val volume :=
    (hMLD i).integrable (by norm_num)
  have hSpatialInt (i : Fin n) :
      IntegrableOn (fun y => (T y)⁻¹ • Dw (ξ y) i) C.val volume := by
    simpa only [D, Fin.addCases_left] using hDInt (Fin.castAdd 1 i)
  have hTimeInt : IntegrableOn
      (fun y => -((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (ξ y) i)) C.val volume := by
    simpa only [D, Fin.addCases_right] using hDInt (Fin.natAdd n (0 : Fin 1))
  refine ⟨⟨hWInt.locallyIntegrableOn, fun i => (hDInt i).locallyIntegrableOn, ?_⟩, hMLW, hMLD⟩
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro φ hφ hcφ hsφ
    simp only [W, D, Fin.addCases_left]
    exact cone_spatial_weak hw.1 C hCratio hWInt hSpatialInt j φ hφ hcφ hsφ
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    intro φ hφ hcφ hsφ
    simp only [W, D, Fin.addCases_right]
    exact cone_time_weak (le_trans (by decide : 1 ≤ 2) hn) B
      (volume_unit_coordinate_face_ne_top n)
      (fun x hx i => ((mem_unit_coordinate_face_iff x).mp hx i).le)
      hw C hCratio hWInt hTimeInt φ hφ hcφ hsφ

private theorem cone_cap_trace {n q : ℕ} (B : OpenDomain n)
    {w : Domain n → Ambient q} (hw : MemLp w 2 (volume.restrict B.val))
    (W : Domain (n + 1) → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ x ∈ B.val, ∀ r ∈ Ioc (0 : ℝ) 1,
      W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)) = w x) →
    ∀ (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) 1),
      ∃ H : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ r : Icc ρ 1, H r = hw.toLp w) ∧
        (∀ r : Icc ρ 1,
          ∃ hr : MemLp (fun x => W (e.symm (r.val • x,
              EuclideanSpace.single (0 : Fin 1) r.val))) 2 (volume.restrict B.val),
            H r = hr.toLp (fun x => W (e.symm (r.val • x,
              EuclideanSpace.single (0 : Fin 1) r.val)))) ∧
        H ⟨1, hρ.2.le, le_rfl⟩ = hw.toLp w ∧
        ∀ K : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)),
          (∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo ρ 1,
            ∃ hslice : MemLp (fun x => W (e.symm (r • x,
                EuclideanSpace.single (0 : Fin 1) r))) 2 (volume.restrict B.val),
              K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp
                (fun x => W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)))) → K = H := by
  intro e hRay ρ hρ
  let H : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)) :=
    ContinuousMap.const _ (hw.toLp w)
  have hRows (r : Icc ρ 1) :
      ∃ hr : MemLp (fun x => W (e.symm (r.val • x,
          EuclideanSpace.single (0 : Fin 1) r.val))) 2 (volume.restrict B.val),
        H r = hr.toLp (fun x => W (e.symm (r.val • x,
          EuclideanSpace.single (0 : Fin 1) r.val))) := by
    have heq : w =ᵐ[volume.restrict B.val] (fun x => W (e.symm (r.val • x,
        EuclideanSpace.single (0 : Fin 1) r.val))) := by
      filter_upwards [ae_restrict_mem B.property.measurableSet] with x hx
      exact (hRay x hx r.val ⟨lt_of_lt_of_le hρ.1 r.property.1, r.property.2⟩).symm
    refine ⟨hw.ae_eq heq, ?_⟩
    exact hw.toLp_congr _ heq
  refine ⟨H, fun _ => rfl, hRows, rfl, ?_⟩
  intro K hK
  let f : Domain n × ℝ → Ambient q := fun p =>
    W (e.symm (p.2 • p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  have hH : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo ρ 1,
      ∃ hs : MemLp (fun x => f (x,r)) 2 (volume.restrict B.val),
        H ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => f (x,r)) :=
    Eventually.of_forall fun r hr => hRows ⟨r, hr.1.le, hr.2.le⟩
  exact continuous_lp_curves_eq_of_ae_interior_slices (f := f)
    (volume.restrict B.val) hρ.2 H K hH hK

theorem result {n q : ℕ} (hn : 2 ≤ n)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w Dw) :
    let B : OpenDomain n :=
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let C : OpenDomain (n + 1) :=
      ⟨T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ i : Fin n, {y : Domain (n + 1) | |X y i| < T y},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_lt (((EuclideanSpace.proj i).continuous.comp
            (continuous_fst.comp e.continuous)).abs)
            ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous))))⟩
    let W : Domain (n + 1) → Ambient q := fun y => w (ξ y)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun i : Fin n => (T y)⁻¹ • Dw (ξ y) i)
        (fun _last : Fin 1 => -((T y)⁻¹ • (∑ i : Fin n, (ξ y) i • Dw (ξ y) i)))
    MemW12 C W D ∧
    (∀ y ∈ C.val, ξ y ∈ B.val) ∧
    (∀ (ψ : Domain (n + 1) → ℝ≥0∞), AEMeasurable ψ (volume.restrict C.val) →
      (∫⁻ y in C.val, ψ y) =
        ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ n) *
          ∫⁻ x in B.val, ψ (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r))) ∧
    Integrable (fun y => ‖W y‖ ^ 2) (volume.restrict C.val) ∧
    (∫ y in C.val, ‖W y‖ ^ 2) =
      ((n : ℝ) + 1)⁻¹ * ∫ x in B.val, ‖w x‖ ^ 2 ∧
    Integrable (fun y => hsNormSq (D y)) (volume.restrict C.val) ∧
    (∫ y in C.val, hsNormSq (D y)) =
      ((n : ℝ) - 1)⁻¹ * ∫ x in B.val,
        hsNormSq (Dw x) + ‖∑ i : Fin n, x i • Dw x i‖ ^ 2 ∧
    (∫ y in C.val, hsNormSq (D y)) ≤
      (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Dw x) ∧
    (∀ x ∈ B.val, ∀ r ∈ Ioc (0 : ℝ) 1,
      W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)) = w x) ∧
    ∀ (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) 1),
      ∃ H : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ r : Icc ρ 1, H r = hw.2.1.toLp w) ∧
        (∀ r : Icc ρ 1,
          ∃ hr : MemLp (fun x => W (e.symm (r.val • x,
              EuclideanSpace.single (0 : Fin 1) r.val))) 2 (volume.restrict B.val),
            H r = hr.toLp (fun x => W (e.symm (r.val • x,
              EuclideanSpace.single (0 : Fin 1) r.val)))) ∧
        H ⟨1, hρ.2.le, le_rfl⟩ = hw.2.1.toLp w ∧
        ∀ K : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)),
          (∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo ρ 1,
            ∃ hslice : MemLp (fun x => W (e.symm (r • x,
                EuclideanSpace.single (0 : Fin 1) r))) 2 (volume.restrict B.val),
              K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp
                (fun x => W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)))) → K = H := by
  intro B e X T ξ C W D
  have hCset : C.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |X y i| < T y} := by
    ext y
    simp only [C, mem_inter_iff, mem_preimage, mem_iInter, mem_setOf_eq]
  have hCratio : C.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧ ξ y ∈ B.val} := by
    rw [hCset]
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (X y)).mpr hy.2⟩
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (X y)).mp hy.2⟩
  have hRay : ∀ x ∈ B.val, ∀ r ∈ Ioc (0 : ℝ) 1,
      W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)) = w x := by
    intro x _ r hr
    dsimp only [W, ξ, T, X]
    simp only [e.apply_symm_apply, PiLp.single_apply, ite_true]
    rw [smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
  have hData := native_unit_face_cone_l2_energy_data hn hw.2.1 hw.2.2
  refine ⟨cone_memW12 hn hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRay, ?_⟩
  · intro y hy
    exact (hCratio ▸ hy).2
  · intro ψ hψ
    rw [hCratio] at hψ ⊢
    exact lintegral_native_positive_cone B.property.measurableSet
      (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) (fun _ ht => ht.1) hψ
  · rw [hCset]
    exact hData.2.2.1
  · rw [hCset]
    exact hData.2.2.2.1
  · rw [hCset]
    exact hData.2.2.2.2.1
  · rw [hCset]
    exact hData.2.2.2.2.2.1
  · rw [hCset]
    exact hData.2.2.2.2.2.2
  · exact cone_cap_trace B hw.2.1 W hRay

end StratificationTheory.Providers.CubicalFaceConeExtensionV2
