module

public import StratificationTheory.Foundation.CoordinatePiecewiseSobolevData
public import StratificationTheory.Foundation.ContinuousLpTraceGluing
import StratificationTheory.Foundation.ContinuousRadialCutoffLimit
import StratificationTheory.Foundation.CylinderTimeTests
import StratificationTheory.Foundation.CylinderSobolevCollar
import HarmonicMaps.Analysis.VariableMollificationL2
import HarmonicMaps.Analysis.SobolevCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.ProjIcc

/-!
# Weak gluing of adjacent native coordinate rectangles

Matching continuous L2 traces cancel the time boundary flux of the original
half-rectangle weak gradients. The displayed whole map and all columns are
the literal time-piecewise original fields.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace StratificationTheory

private theorem coordinate_line_affine {n : ℕ} (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    e.symm (x, EuclideanSpace.single (0 : Fin 1) t) =
      e.symm (x, 0) + t • EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1 := by
  intro e
  apply e.injective
  rw [map_add, map_smul, e.apply_symm_apply, e.apply_symm_apply, finAddEquivProd_time_basis]
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  congr 1
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp

private theorem continuous_native_test_L2_curve {n q : ℕ}
    (μ : Measure (Domain n)) [IsFiniteMeasure μ]
    {a b : ℝ} {φ : Domain (n + 1) → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (j : Fin q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∃ V : C(Icc a b, Lp (Ambient q) 2 μ), ∀ t : Icc a b,
      ∃ ht : MemLp (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) •
          EuclideanSpace.single j (1 : ℝ)) 2 μ,
        V t = ht.toLp (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) •
          EuclideanSpace.single j (1 : ℝ)) := by
  intro e
  let P : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  have hP : Continuous P := by
    have hPAff : P = (fun p : Domain n × ℝ => e.symm (p.1, 0) +
        p.2 • EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) := by
      funext p
      exact coordinate_line_affine p.1 p.2
    rw [hPAff]
    exact (e.symm.continuous.comp (continuous_fst.prodMk continuous_const)).add
      (continuous_snd.smul continuous_const)
  let A : ℝ → Domain n → Ambient q := fun t x =>
    φ (P (x,t)) • EuclideanSpace.single j (1 : ℝ)
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hcφ
  have hMA (t : ℝ) (x : Domain n) : ‖A t x‖ ≤ M := by
    dsimp only [A]
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    exact hM _
  have hMem (t : ℝ) : MemLp (A t) 2 μ := by
    have hTop : MemLp (fun x => φ (P (x,t))) ∞ μ :=
      memLp_top_of_bound ((hφ.comp (hP.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
        M (Eventually.of_forall fun x => hM _)
    have h := (memLp_const (EuclideanSpace.single j (1 : ℝ)) :
      MemLp (fun _ : Domain n => EuclideanSpace.single j (1 : ℝ)) 2 μ).smul
        (r := (2 : ℝ≥0∞)) hTop
    exact h.ae_eq (Eventually.of_forall fun _ => rfl)
  let V : Icc a b → Lp (Ambient q) 2 μ := fun t => (hMem t.val).toLp (A t.val)
  have hV : Continuous V := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hInt (t : Icc a b) : Integrable (fun x => ‖A t.val x - A t₀.val x‖ ^ 2) μ :=
      ((hMem t.val).sub (hMem t₀.val)).integrable_norm_pow (by decide)
    have hMeas (t : Icc a b) : AEStronglyMeasurable
        (fun x => ‖A t.val x - A t₀.val x‖ ^ 2) μ := (hInt t).aestronglyMeasurable
    have hBound (t : Icc a b) : ∀ᵐ x ∂μ,
        ‖‖A t.val x - A t₀.val x‖ ^ 2‖ ≤ (2 * M) ^ 2 := by
      apply Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by linarith only [hMA t.val x, hMA t₀.val x])
    have hPoint : ∀ᵐ x ∂μ, Tendsto (fun t : Icc a b => ‖A t.val x - A t₀.val x‖ ^ 2)
        (𝓝 t₀) (𝓝 (0 : ℝ)) := by
      apply Eventually.of_forall
      intro x
      have hA : Continuous (fun t : Icc a b => A t.val x) :=
        (hφ.comp (hP.comp (continuous_const.prodMk continuous_subtype_val))).smul continuous_const
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((hA.tendsto t₀).sub_const (A t₀.val x)).norm.pow 2
    have hconv := tendsto_integral_filter_of_dominated_convergence
      (fun _ : Domain n => (2 * M) ^ 2) (Eventually.of_forall hMeas)
      (Eventually.of_forall hBound) (integrable_const _) hPoint
    have hNorm (t : Icc a b) : ‖V t - V t₀‖ ^ 2 = ∫ x, ‖A t.val x - A t₀.val x‖ ^ 2 ∂μ := by
      have hd : MemLp (fun x => A t.val x - A t₀.val x) 2 μ :=
        ((hMem t.val).sub (hMem t₀.val)).ae_eq (Eventually.of_forall fun _ => rfl)
      have hEq : V t - V t₀ = hd.toLp (fun x => A t.val x - A t₀.val x) := by
        rw [show V t = (hMem t.val).toLp (A t.val) from rfl,
          show V t₀ = (hMem t₀.val).toLp (A t₀.val) from rfl,
          ← (hMem t.val).toLp_sub (hMem t₀.val)]
        rfl
      rw [hEq, Lp.norm_toLp]
      exact (integral_norm_sq_eq_eLpNorm_two_toReal_sq hd).symm
    have hsquare : Tendsto (fun t : Icc a b => ‖V t - V t₀‖ ^ 2) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
      simpa only [integral_zero, ← hNorm] using hconv
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact ⟨⟨V, hV⟩, fun t => ⟨hMem t.val, rfl⟩⟩

private theorem exists_continuous_native_trace_flux {n q : ℕ}
    (μ : Measure (Domain n)) [IsFiniteMeasure μ] {a b : ℝ}
    {φ : Domain (n + 1) → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (j : Fin q) (H : C(Icc a b, Lp (Ambient q) 2 μ)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∃ J : C(Icc a b, ℝ), ∀ t : Icc a b,
      Integrable (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) * (H t x) j) μ ∧
      J t = ∫ x, φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) * (H t x) j ∂μ := by
  intro e
  obtain ⟨V, hV⟩ := continuous_native_test_L2_curve μ hφ hcφ j
  let J : C(Icc a b, ℝ) := ⟨fun t => inner ℝ (H t) (V t), H.continuous.inner V.continuous⟩
  refine ⟨J, ?_⟩
  intro t
  obtain ⟨hvt, hvtEq⟩ := hV t
  have hEq : (fun x => inner ℝ (H t x) (V t x)) =ᵐ[μ]
      (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) * (H t x) j) := by
    have hraw : (fun x => V t x) =ᵐ[μ]
        (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) •
          EuclideanSpace.single j (1 : ℝ)) := by
      rw [hvtEq]
      exact hvt.coeFn_toLp
    filter_upwards [hraw] with x hx
    rw [hx, real_inner_smul_right, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  exact ⟨(L2.integrable_inner (H t) (V t)).congr hEq, by
    change inner ℝ (H t) (V t) = _
    rw [L2.inner_def, integral_congr_ae hEq]⟩

private theorem shifted_cutoff_data (s : ℝ) (δ : PositiveRadius) :
    let χ : ℝ → ℝ := fun r => 1 - Real.smoothTransition ((r - s) / δ.val)
    ContDiff ℝ ∞ χ ∧
    (∀ r, χ r ∈ Icc (0 : ℝ) 1) ∧
    (∀ r, r ≤ s → χ r = 1) ∧
    (∀ r, s + δ.val ≤ r → χ r = 0) ∧
    (∀ r, deriv χ r ≤ 0) ∧
    tsupport (deriv χ) ⊆ Icc s (s + δ.val) ∧
    (∫ r in s..(s + δ.val), deriv χ r) = -1 := by
  intro χ
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ.val))
  have hχone (r : ℝ) (hr : r ≤ s) : χ r = 1 := by
    rw [show χ r = 1 - Real.smoothTransition ((r - s) / δ.val) from rfl,
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) δ.property.le), sub_zero]
  have hχzero (r : ℝ) (hr : s + δ.val ≤ r) : χ r = 0 := by
    rw [show χ r = 1 - Real.smoothTransition ((r - s) / δ.val) from rfl,
      Real.smoothTransition.one_of_one_le, sub_self]
    exact (le_div_iff₀ δ.property).mpr (by linarith only [hr])
  have hDeriv (r : ℝ) : deriv χ r =
      -(deriv Real.smoothTransition ((r - s) / δ.val)) / δ.val := by
    have h := ((hasDerivAt_id r).sub_const s).div_const δ.val
    have hs := ((Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).differentiable
      one_ne_zero ((r - s) / δ.val)).hasDerivAt.comp r h
    have hh := (hasDerivAt_const r (1 : ℝ)).sub hs
    simpa only [χ, Function.comp_def, Pi.sub_def, id_eq, zero_sub, div_eq_mul_inv,
      one_mul, neg_mul] using hh.deriv
  have hNeg (r : ℝ) : deriv χ r ≤ 0 := by
    rw [hDeriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr Real.smoothTransition.monotone.deriv_nonneg) δ.property.le
  have hZero (r : ℝ) (hr : r ∉ Icc s (s + δ.val)) : deriv χ r = 0 := by
    rw [hDeriv, smoothTransition_deriv_eq_zero, neg_zero, zero_div]
    intro harg
    apply hr
    constructor
    · have h := (le_div_iff₀ δ.property).mp harg.1
      linarith only [h]
    · have h := (div_le_one δ.property).mp harg.2
      linarith only [h]
  have hSupp : tsupport (deriv χ) ⊆ Icc s (s + δ.val) :=
    closure_minimal (fun r hr => by by_contra hn; exact hr (hZero r hn)) isClosed_Icc
  refine ⟨hχ, ?_, hχone, hχzero, hNeg, hSupp, ?_⟩
  · intro r
    have h0 := Real.smoothTransition.nonneg ((r - s) / δ.val)
    have h1 := Real.smoothTransition.le_one ((r - s) / δ.val)
    constructor <;> dsimp only [χ] <;> linarith only [h0, h1]
  · rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => (hχ.differentiable (by norm_num)) _)
      ((hχ.continuous_deriv (by norm_num)).intervalIntegrable _ _),
      hχzero _ le_rfl, hχone _ le_rfl]
    norm_num

private theorem shifted_cutoff_flux_sample (s : ℝ) (δ : PositiveRadius)
    (w : ℝ → ℝ) (hw : Continuous w) :
    let χ : ℝ → ℝ := fun r => 1 - Real.smoothTransition ((r - s) / δ.val)
    ∃ ξ ∈ Icc s (s + δ.val),
      (∫ r in s..(s + δ.val), deriv χ r * w r) = -w ξ := by
  intro χ
  have hData := shifted_cutoff_data s δ
  have hcont : Continuous (deriv χ) := hData.1.continuous_deriv (by norm_num)
  obtain ⟨ξ, hξ, hEq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := volume) hw.continuousOn
    (hcont.neg.intervalIntegrable s (s + δ.val))
    (fun r _ => neg_nonneg.mpr (hData.2.2.2.2.1 r))
  have hMass : (∫ r in s..(s + δ.val), -deriv χ r) = 1 := by
    rw [intervalIntegral.integral_neg, hData.2.2.2.2.2.2]
    norm_num
  dsimp only [Pi.neg_apply] at hEq
  rw [hMass, mul_one] at hEq
  have hNeg : (∫ r in s..(s + δ.val), w r * -deriv χ r) =
      -(∫ r in s..(s + δ.val), deriv χ r * w r) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  rw [hNeg] at hEq
  refine ⟨ξ, ?_, by linarith only [hEq]⟩
  simpa only [uIcc_of_le (le_add_of_nonneg_right δ.property.le)] using hξ

private theorem tendsto_shifted_cutoff_flux {ι : Type*} {l : Filter ι}
    (s : ι → ℝ) (δ : ι → PositiveRadius) {b : ℝ}
    (hs : Tendsto s l (𝓝 b)) (hδ : Tendsto (fun k => (δ k).val) l (𝓝 (0 : ℝ)))
    (w : ℝ → ℝ) (hw : Continuous w) :
    Tendsto (fun k => ∫ r in s k..(s k + (δ k).val),
      deriv (fun r => 1 - Real.smoothTransition ((r - s k) / (δ k).val)) r * w r)
      l (𝓝 (-w b)) := by
  choose ξ hξ hEq using fun k => shifted_cutoff_flux_sample (s k) (δ k) w hw
  have hupper : Tendsto (fun k => s k + (δ k).val) l (𝓝 b) := by
    simpa only [add_zero] using hs.add hδ
  have hξlim : Tendsto ξ l (𝓝 b) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hs hupper (fun k => (hξ k).1) (fun k => (hξ k).2)
  simpa only [hEq, Function.comp_def, Pi.neg_apply] using ((hw.tendsto b).comp hξlim).neg

private theorem exists_continuous_native_raw_flux {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)] {a b : ℝ}
    (u : Domain (n + 1) → Ambient q) (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => u ((EuclideanSpace.finAddEquivProd
          (𝕜 := ℝ) (n := n) (m := 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
          (volume.restrict U.val),
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u ((EuclideanSpace.finAddEquivProd
          (𝕜 := ℝ) (n := n) (m := 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t))))
    {φ : Domain (n + 1) → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (j : Fin q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∃ J : C(Icc a b, ℝ),
      (∀ t : Icc a b, J t = ∫ x in U.val,
        φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)) * (H t x) j) ∧
      ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        Integrable (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) *
          (u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) j) (volume.restrict U.val) ∧
        J ⟨t, ht.1.le, ht.2.le⟩ = ∫ x in U.val,
          φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) *
            (u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) j := by
  intro e
  obtain ⟨J, hJ⟩ := exists_continuous_native_trace_flux (volume.restrict U.val) hφ hcφ j H
  refine ⟨J, fun t => (hJ t).2, ?_⟩
  filter_upwards [hH] with t ht htI
  obtain ⟨hs, hsEq⟩ := ht htI
  let tI : Icc a b := ⟨t, htI.1.le, htI.2.le⟩
  have hraw : (fun x => H tI x) =ᵐ[volume.restrict U.val]
      (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
    rw [show H tI = hs.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) from hsEq]
    exact hs.coeFn_toLp
  have hEq : (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) * (H tI x) j) =ᵐ[
      volume.restrict U.val] (fun x => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) *
        (u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) j) := by
    filter_upwards [hraw] with x hx
    rw [hx]
  exact ⟨(hJ tI).1.congr hEq, (hJ tI).2.trans (integral_congr_ae hEq)⟩

private theorem native_cutoff_flux_integral {n q : ℕ} (U : OpenDomain n) {a b s : ℝ}
    (δ : PositiveRadius) (hBand : Icc s (s + δ.val) ⊆ Ioo a b)
    (u : Domain (n + 1) → Ambient q) {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hSupp : tsupport (deriv κ) ⊆ Icc s (s + δ.val))
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (i : Fin (n + 1)) (j : Fin q) (E : ℝ → ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
      ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
    let Ω := {y : Domain (n + 1) | (e y).1 ∈ U.val ∧ T y ∈ Ioo a b}
    let χ : Domain (n + 1) → ℝ := fun y => κ (T y)
    let hχ : ContDiff ℝ ∞ χ := hκ.comp T.contDiff
    IntegrableOn u Ω volume →
    (∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      E t = ∫ x in U.val, φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) *
        (u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) j) →
    (∫ y in Ω, (φ y * coordinateDerivative χ hχ i y) * (u y) j) =
      T (EuclideanSpace.single i 1) * ∫ t in s..(s + δ.val), deriv κ t * E t := by
  intro e T Ω χ hχ hu hRaw
  let P : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  have hTP (x : Domain n) (t : ℝ) : T (P (x,t)) = t := by
    change (e (P (x,t))).2 0 = t
    dsimp only [P]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
  have hCutD (y : Domain (n + 1)) : coordinateDerivative χ hχ i y =
      deriv κ (T y) * T (EuclideanSpace.single i 1) := by
    have hD := ((hκ.differentiable (by simp) (T y)).hasDerivAt).comp_hasFDerivAt y T.hasFDerivAt
    change fderiv ℝ (κ ∘ T) y (EuclideanSpace.single i 1) = _
    rw [hD.fderiv]
    rfl
  have huj : IntegrableOn (fun y => (u y) j) Ω volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp hu
  have hCoeff : MemLp (fun y => φ y * coordinateDerivative χ hχ i y) ∞
      (volume.restrict Ω) :=
    (hφ.continuous.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
      hcφ.mul_right _
  have hBI : IntegrableOn (fun y => (φ y * coordinateDerivative χ hχ i y) * (u y) j) Ω volume :=
    huj.smul_of_top_right hCoeff
  have hB := integral_native_rectangle U.property.measurableSet
    (measurableSet_Ioo (a := a) (b := b)) hBI
  change (∫ y in Ω, (φ y * coordinateDerivative χ hχ i y) * (u y) j) =
    ∫ t in Ioo a b, ∫ x in U.val,
      (φ (P (x,t)) * coordinateDerivative χ hχ i (P (x,t))) * (u (P (x,t))) j at hB
  have hRect : (∫ y in Ω, (φ y * coordinateDerivative χ hχ i y) * (u y) j) =
      T (EuclideanSpace.single i 1) * ∫ t in Ioo a b, deriv κ t * E t := by
    rw [hB, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hRaw.filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hRow : (∫ x in U.val, (φ (P (x,t)) * coordinateDerivative χ hχ i (P (x,t))) *
        (u (P (x,t))) j) = T (EuclideanSpace.single i 1) * deriv κ t *
          ∫ x in U.val, φ (P (x,t)) * (u (P (x,t))) j := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change (φ (P (x,t)) * coordinateDerivative χ hχ i (P (x,t))) * (u (P (x,t))) j = _
      rw [hCutD, hTP]
      ring
    change (∫ x in U.val, (φ (P (x,t)) * coordinateDerivative χ hχ i (P (x,t))) *
      (u (P (x,t))) j) = _
    rw [hRow, ← ht htI]
    ring
  have hsupport : Function.support (fun t => deriv κ t * E t) ⊆ Icc s (s + δ.val) := by
    intro t ht
    exact hSupp (subset_tsupport _ (mul_ne_zero_iff.mp ht).1)
  have hFull : (∫ t in Ioo a b, deriv κ t * E t) = ∫ t, deriv κ t * E t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun hm => ht (hBand (hsupport hm)))
  have hBandInt : (∫ t in Icc s (s + δ.val), deriv κ t * E t) = ∫ t, deriv κ t * E t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun hm => ht (hsupport hm))
  rw [hRect, hFull, ← hBandInt, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_add_of_nonneg_right δ.property.le)]

private theorem tendsto_integral_bounded_multiplier {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Integrable g μ)
    (a : ℕ → α → ℝ) (ha : ∀ k, AEStronglyMeasurable (a k) μ)
    (hb : ∀ k, ∀ᵐ x ∂μ, |a k x| ≤ 1)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun k => a k x) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun k => ∫ x, a k x * g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun k => (ha k).mul hg.aestronglyMeasurable) hg.norm
    (fun k => (hb k).mono fun x hx => by
      change ‖a k x * g x‖ ≤ ‖g x‖
      rw [norm_mul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (one_mul _))
    (ht.mono fun x hx => by simpa only [one_mul, Pi.mul_apply] using hx.mul_const (g x))
  exact h

private theorem weak_gradient_mul_cutoff_scalar {n q : ℕ}
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemW12 Ω u D) (hfinite : (volume : Measure (Domain n)) Ω.val ≠ ⊤)
    (φ χ : Domain n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hcφ : HasCompactSupport φ)
    (hs : tsupport (fun x => φ x * χ x) ⊆ Ω.val) (i : Fin n) (j : Fin q) :
    (∫ x in Ω.val, χ x * (coordinateDerivative φ hφ i x * (u x) j)) +
      (∫ x in Ω.val, (φ x * coordinateDerivative χ hχ i x) * (u x) j) =
        -(∫ x in Ω.val, χ x * (φ x * (D x i) j)) := by
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hfinite
  let ψ : Domain n → ℝ := fun x => φ x * χ x
  have hψ : ContDiff ℝ ∞ ψ := hφ.mul hχ
  have hcψ : HasCompactSupport ψ := hcφ.mul_right
  have hweak := hu.1.2.2 i ψ hψ hcψ hs
  have hscalar := congrArg (EuclideanSpace.proj (𝕜 := ℝ) j) hweak
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm
      (hu.1.integrable_test_derivative i hψ hcψ hs), map_neg,
    ← (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm
      (hu.1.integrable_test_gradient i hψ hcψ hs)] at hscalar
  change (∫ x in Ω.val, coordinateDerivative ψ hψ i x * (u x) j) =
    -(∫ x in Ω.val, ψ x * (D x i) j) at hscalar
  have huI : IntegrableOn (fun x => (u x) j) Ω.val :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp (hu.2.1.integrable (by norm_num))
  have hAI : IntegrableOn (fun x => χ x * (coordinateDerivative φ hφ i x * (u x) j)) Ω.val := by
    have hc : HasCompactSupport (coordinateDerivative φ hφ i) :=
      hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have hw : MemLp (fun x => χ x * coordinateDerivative φ hφ i x) ∞ (volume.restrict Ω.val) :=
      (hχ.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
        hc.mul_left _
    have hh : IntegrableOn (fun x => (χ x * coordinateDerivative φ hφ i x) * (u x) j) Ω.val :=
      huI.smul_of_top_right hw
    simpa only [mul_assoc] using hh
  have hBI : IntegrableOn (fun x => (φ x * coordinateDerivative χ hχ i x) * (u x) j) Ω.val := by
    have hw : MemLp (fun x => φ x * coordinateDerivative χ hχ i x) ∞ (volume.restrict Ω.val) :=
      (hφ.continuous.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
        hcφ.mul_right _
    exact huI.smul_of_top_right hw
  have hpoint (x : Domain n) : coordinateDerivative ψ hψ i x * (u x) j =
      χ x * (coordinateDerivative φ hφ i x * (u x) j) +
        (φ x * coordinateDerivative χ hχ i x) * (u x) j := by
    rw [coordinateDerivative_mul hφ hχ]
    ring
  simp_rw [hpoint] at hscalar
  rw [integral_add hAI hBI] at hscalar
  convert hscalar using 1
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by dsimp only [ψ]; ring


private theorem coordinate_piecewise_weak_test_scalar {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (u v : Domain (n + 1) → Ambient q) (Du Dv : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
      ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
    let Ω : ℝ → ℝ → OpenDomain (n + 1) := fun d f =>
      ⟨{y | (e y).1 ∈ U.val ∧ T y ∈ Ioo d f},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage T.continuous)⟩
    MemW12 (Ω a b) u Du → MemW12 (Ω b c) v Dv →
    ∀ (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
      (K : C(Icc b c, Lp (Ambient q) 2 (volume.restrict U.val))),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hs : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
            (volume.restrict U.val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b c,
        ∃ hs : MemLp (fun x => v (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
            (volume.restrict U.val),
          K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => v (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
      H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbc.le⟩ →
      ∀ (i : Fin (n + 1)) (j : Fin q) (φ : Domain (n + 1) → ℝ)
        (hφ : ContDiff ℝ ∞ φ), HasCompactSupport φ → tsupport φ ⊆ (Ω a c).val →
      (∫ y in (Ω a b).val, coordinateDerivative φ hφ i y * (u y) j) +
        (∫ y in (Ω b c).val, coordinateDerivative φ hφ i y * (v y) j) =
      -((∫ y in (Ω a b).val, φ y * (Du y i) j) +
        ∫ y in (Ω b c).val, φ y * (Dv y i) j) := by
  intro e T Ω hu hv H K hH hK hmatch i j φ hφ hcφ hsφ
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ :=
    isFiniteMeasure_restrict.mp inferInstance
  have hfinite (d f : ℝ) : (volume : Measure (Domain (n + 1))) (Ω d f).val ≠ ⊤ := by
    change (volume : Measure (Domain (n + 1)))
      {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo d f} ≠ ⊤
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict (Ω a b).val) := isFiniteMeasure_restrict.mpr (hfinite a b)
  letI : IsFiniteMeasure (volume.restrict (Ω b c).val) := isFiniteMeasure_restrict.mpr (hfinite b c)
  have huI : IntegrableOn u (Ω a b).val volume := hu.2.1.integrable (by norm_num)
  have hvI : IntegrableOn v (Ω b c).val volume := hv.2.1.integrable (by norm_num)
  let d : ℝ := min ((b - a) / 8) ((c - b) / 8)
  have hd : 0 < d := lt_min (by linarith only [hab]) (by linarith only [hbc])
  let ε : ℕ → PositiveRadius := fun k => ⟨d / ((k : ℝ) + 1), by positivity⟩
  have hεle (k : ℕ) : (ε k).val ≤ d :=
    div_le_self hd.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hεL (k : ℕ) : (ε k).val ≤ (b - a) / 8 := (hεle k).trans (min_le_left _ _)
  have hεR (k : ℕ) : (ε k).val ≤ (c - b) / 8 := (hεle k).trans (min_le_right _ _)
  have hεlim : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [ε, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
  let sL : ℕ → ℝ := fun k => b - 2 * (ε k).val
  let sR : ℕ → ℝ := fun k => b + (ε k).val
  let κL : ℕ → ℝ → ℝ := fun k r => 1 - Real.smoothTransition ((r - sL k) / (ε k).val)
  let κR : ℕ → ℝ → ℝ := fun k r => 1 - Real.smoothTransition ((r - sR k) / (ε k).val)
  let χL : ℕ → Domain (n + 1) → ℝ := fun k y => κL k (T y)
  let χR : ℕ → Domain (n + 1) → ℝ := fun k y => 1 - κR k (T y)
  have hκL (k : ℕ) : ContDiff ℝ ∞ (κL k) := (shifted_cutoff_data (sL k) (ε k)).1
  have hκR (k : ℕ) : ContDiff ℝ ∞ (κR k) := (shifted_cutoff_data (sR k) (ε k)).1
  have hχL (k : ℕ) : ContDiff ℝ ∞ (χL k) := (hκL k).comp T.contDiff
  have hχR (k : ℕ) : ContDiff ℝ ∞ (χR k) := contDiff_const.sub ((hκR k).comp T.contDiff)
  have hχLb (k : ℕ) : ∀ᵐ y ∂volume.restrict (Ω a b).val, |χL k y| ≤ 1 := by
    apply Eventually.of_forall
    intro y
    have h := (shifted_cutoff_data (sL k) (ε k)).2.1 (T y)
    exact abs_le.mpr ⟨by linarith only [h.1], h.2⟩
  have hχRb (k : ℕ) : ∀ᵐ y ∂volume.restrict (Ω b c).val, |χR k y| ≤ 1 := by
    apply Eventually.of_forall
    intro y
    have h := (shifted_cutoff_data (sR k) (ε k)).2.1 (T y)
    apply abs_le.mpr
    constructor <;> dsimp only [χR] <;> linarith only [h.1, h.2]
  have hχLlim : ∀ᵐ y ∂volume.restrict (Ω a b).val,
      Tendsto (fun k => χL k y) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (Ω a b).property.measurableSet] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [hεlim.eventually (Iio_mem_nhds (by linarith only [hy.2.2] :
      (0 : ℝ) < (b - T y) / 2))] with k hk
    symm
    exact (shifted_cutoff_data (sL k) (ε k)).2.2.1 (T y) (by dsimp only [sL]; linarith only [hk])
  have hχRlim : ∀ᵐ y ∂volume.restrict (Ω b c).val,
      Tendsto (fun k => χR k y) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (Ω b c).property.measurableSet] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [hεlim.eventually (Iio_mem_nhds (by linarith only [hy.2.1] :
      (0 : ℝ) < (T y - b) / 2))] with k hk
    change 1 = 1 - κR k (T y)
    have hzero : κR k (T y) = 0 := (shifted_cutoff_data (sR k) (ε k)).2.2.2.1 (T y)
      (by dsimp only [sR]; linarith only [hk])
    rw [hzero, sub_zero]
  have htestL (k : ℕ) : tsupport (fun y => φ y * χL k y) ⊆ (Ω a b).val := by
    have hside : tsupport (χL k) ⊆ {y | T y ≤ sL k + (ε k).val} := by
      apply closure_minimal _ (isClosed_le T.continuous continuous_const)
      intro y hy
      by_contra hn
      have hh := (shifted_cutoff_data (sL k) (ε k)).2.2.2.1 (T y) (le_of_lt (lt_of_not_ge hn))
      exact hy hh
    intro y hy
    have hfull := hsφ (tsupport_mul_subset_left hy)
    have hside' := hside (tsupport_mul_subset_right hy)
    refine ⟨hfull.1, hfull.2.1, ?_⟩
    change T y ≤ b - 2 * (ε k).val + (ε k).val at hside'
    linarith only [hside', (ε k).property]
  have htestR (k : ℕ) : tsupport (fun y => φ y * χR k y) ⊆ (Ω b c).val := by
    have hside : tsupport (χR k) ⊆ {y | sR k ≤ T y} := by
      apply closure_minimal _ (isClosed_le continuous_const T.continuous)
      intro y hy
      by_contra hn
      have hh : κR k (T y) = 1 :=
        (shifted_cutoff_data (sR k) (ε k)).2.2.1 (T y) (le_of_lt (lt_of_not_ge hn))
      apply hy
      change 1 - κR k (T y) = 0
      rw [hh, sub_self]
    intro y hy
    have hfull := hsφ (tsupport_mul_subset_left hy)
    have hside' := hside (tsupport_mul_subset_right hy)
    refine ⟨hfull.1, ?_, hfull.2.2⟩
    change b + (ε k).val ≤ T y at hside'
    linarith only [hside', (ε k).property]
  have hBandL (k : ℕ) : Icc (sL k) (sL k + (ε k).val) ⊆ Ioo a b := by
    intro t ht
    dsimp only [sL] at ht
    constructor <;> linarith [ht.1, ht.2, hεL k, (ε k).property]
  have hBandR (k : ℕ) : Icc (sR k) (sR k + (ε k).val) ⊆ Ioo b c := by
    intro t ht
    dsimp only [sR] at ht
    constructor <;> linarith [ht.1, ht.2, hεR k, (ε k).property]
  have hφL : MemLp φ ∞ (volume.restrict (Ω a b).val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hφR : MemLp φ ∞ (volume.restrict (Ω b c).val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφL : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict (Ω a b).val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hdφR : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict (Ω b c).val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have huj := (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp huI
  have hvj := (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp hvI
  have hDuj := (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp
    ((hu.2.2 i).integrable (by norm_num))
  have hDvj := (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp
    ((hv.2.2 i).integrable (by norm_num))
  have hAu : IntegrableOn (fun y => coordinateDerivative φ hφ i y * (u y) j) (Ω a b).val :=
    huj.smul_of_top_right hdφL
  have hAv : IntegrableOn (fun y => coordinateDerivative φ hφ i y * (v y) j) (Ω b c).val :=
    hvj.smul_of_top_right hdφR
  have hCu : IntegrableOn (fun y => φ y * (Du y i) j) (Ω a b).val := hDuj.smul_of_top_right hφL
  have hCv : IntegrableOn (fun y => φ y * (Dv y i) j) (Ω b c).val := hDvj.smul_of_top_right hφR
  have hAulim := tendsto_integral_bounded_multiplier hAu χL
    (fun k => (hχL k).continuous.aestronglyMeasurable) hχLb hχLlim
  have hAvlim := tendsto_integral_bounded_multiplier hAv χR
    (fun k => (hχR k).continuous.aestronglyMeasurable) hχRb hχRlim
  have hCulim := tendsto_integral_bounded_multiplier hCu χL
    (fun k => (hχL k).continuous.aestronglyMeasurable) hχLb hχLlim
  have hCvlim := tendsto_integral_bounded_multiplier hCv χR
    (fun k => (hχR k).continuous.aestronglyMeasurable) hχRb hχRlim
  obtain ⟨Ju, hJu, hJuRaw⟩ := exists_continuous_native_raw_flux U u H hH hφ.continuous hcφ j
  obtain ⟨Jv, hJv, hJvRaw⟩ := exists_continuous_native_raw_flux U v K hK hφ.continuous hcφ j
  let Eu : ℝ → ℝ := IccExtend hab.le Ju
  let Ev : ℝ → ℝ := IccExtend hbc.le Jv
  have hEu : Continuous Eu := Ju.continuous.Icc_extend'
  have hEv : Continuous Ev := Jv.continuous.Icc_extend'
  have hEb : Eu b = Ev b := by
    rw [show Eu b = Ju ⟨b, hab.le, le_rfl⟩ from IccExtend_right hab.le Ju,
      show Ev b = Jv ⟨b, le_rfl, hbc.le⟩ from IccExtend_left hbc.le Jv,
      hJu, hJv, hmatch]
  have hBu (k : ℕ) :
      (∫ y in (Ω a b).val, (φ y * coordinateDerivative (χL k) (hχL k) i y) * (u y) j) =
        T (EuclideanSpace.single i 1) * ∫ t in sL k..(sL k + (ε k).val), deriv (κL k) t * Eu t := by
    apply native_cutoff_flux_integral U (ε k) (hBandL k) u (hκL k)
      (shifted_cutoff_data (sL k) (ε k)).2.2.2.2.2.1 hφ hcφ i j Eu huI
    filter_upwards [hJuRaw] with t ht htI
    rw [show Eu t = Ju ⟨t, htI.1.le, htI.2.le⟩ from IccExtend_of_mem hab.le Ju ⟨htI.1.le, htI.2.le⟩]
    exact (ht htI).2
  have hBv (k : ℕ) :
      (∫ y in (Ω b c).val, (φ y * coordinateDerivative (χR k) (hχR k) i y) * (v y) j) =
        -(T (EuclideanSpace.single i 1) * ∫ t in sR k..(sR k + (ε k).val), deriv (κR k) t * Ev t) := by
    have hRaw : (∫ y in (Ω b c).val,
        (φ y * coordinateDerivative (fun y => κR k (T y)) ((hκR k).comp T.contDiff) i y) * (v y) j) =
          T (EuclideanSpace.single i 1) * ∫ t in sR k..(sR k + (ε k).val), deriv (κR k) t * Ev t := by
      apply native_cutoff_flux_integral U (ε k) (hBandR k) v (hκR k)
        (shifted_cutoff_data (sR k) (ε k)).2.2.2.2.2.1 hφ hcφ i j Ev hvI
      filter_upwards [hJvRaw] with t ht htI
      rw [show Ev t = Jv ⟨t, htI.1.le, htI.2.le⟩ from IccExtend_of_mem hbc.le Jv ⟨htI.1.le, htI.2.le⟩]
      exact (ht htI).2
    rw [← hRaw, ← integral_neg]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    change (φ y * coordinateDerivative (fun z => 1 - κR k (T z)) (hχR k) i y) * (v y) j = _
    simp only [coordinateDerivative, fderiv_const_sub, neg_apply]
    ring
  have hsLlim : Tendsto sL atTop (𝓝 b) := by
    simpa only [sL, mul_zero, sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hεlim)
  have hsRlim : Tendsto sR atTop (𝓝 b) := by
    simpa only [sR, add_zero] using tendsto_const_nhds.add hεlim
  have hBulim := ((tendsto_shifted_cutoff_flux sL ε hsLlim hεlim Eu hEu).const_mul
    (T (EuclideanSpace.single i 1))).congr' (Eventually.of_forall fun k => (hBu k).symm)
  have hBvlim := (((tendsto_shifted_cutoff_flux sR ε hsRlim hεlim Ev hEv).const_mul
    (T (EuclideanSpace.single i 1))).neg).congr' (Eventually.of_forall fun k => (hBv k).symm)
  have hId (k : ℕ) := weak_gradient_mul_cutoff_scalar (Ω a b) u Du hu (hfinite a b)
    φ (χL k) hφ (hχL k) hcφ (htestL k) i j
  have hIv (k : ℕ) := weak_gradient_mul_cutoff_scalar (Ω b c) v Dv hv (hfinite b c)
    φ (χR k) hφ (hχR k) hcφ (htestR k) i j
  have hsumId (k : ℕ) := congrArg₂ (fun x y : ℝ => x + y) (hId k) (hIv k)
  have hleftlim := (hAulim.add hBulim).add (hAvlim.add hBvlim)
  have hrightlim := hCulim.neg.add hCvlim.neg
  have hsum := tendsto_nhds_unique hleftlim
    (hrightlim.congr' (Eventually.of_forall fun k => (hsumId k).symm))
  rw [← hEb] at hsum
  linarith only [hsum]

/-- Matching actual continuous L2 traces glue the original full weak graphs on adjacent
rectangles, with the literal piecewise columns, additive HS energy and one whole trace. -/
theorem memW12_coordinate_piecewise_of_matching_L2_traces {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (u v : Domain (n + 1) → Ambient q) (Du Dv : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
      ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
    let Ω : ℝ → ℝ → OpenDomain (n + 1) := fun d f =>
      ⟨{y | (e y).1 ∈ U.val ∧ T y ∈ Ioo d f},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage T.continuous)⟩
    MemW12 (Ω a b) u Du → MemW12 (Ω b c) v Dv →
    ∀ (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
      (K : C(Icc b c, Lp (Ambient q) 2 (volume.restrict U.val))),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hs : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
            (volume.restrict U.val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b c,
        ∃ hs : MemLp (fun x => v (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
            (volume.restrict U.val),
          K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => v (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
      H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbc.le⟩ →
      let f : Domain (n + 1) → Ambient q := fun y => if T y < b then u y else v y
      let Df : Domain (n + 1) → Gradient (n + 1) q := fun y i => if T y < b then Du y i else Dv y i
      MemW12 (Ω a c) f Df ∧
      (∫ y in (Ω a c).val, hsNormSq (Df y)) =
        (∫ y in (Ω a b).val, hsNormSq (Du y)) + (∫ y in (Ω b c).val, hsNormSq (Dv y)) ∧
      ∃ J : C(Icc a c, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ t : Icc a b, J ⟨t.val, t.property.1, t.property.2.trans hbc.le⟩ = H t) ∧
        (∀ t : Icc b c, J ⟨t.val, hab.le.trans t.property.1, t.property.2⟩ = K t) ∧
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hs : MemLp (fun x => f (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
              (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ =
              hs.toLp (fun x => f (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
  intro e T Ω hu hv H K hH hK hmatch f Df
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := isFiniteMeasure_restrict.mp inferInstance
  have hfinite (d g : ℝ) : (volume : Measure (Domain (n + 1))) (Ω d g).val ≠ ⊤ := by
    change (volume : Measure (Domain (n + 1)))
      {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo d g} ≠ ⊤
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict (Ω a b).val) := isFiniteMeasure_restrict.mpr (hfinite a b)
  letI : IsFiniteMeasure (volume.restrict (Ω b c).val) := isFiniteMeasure_restrict.mpr (hfinite b c)
  letI : IsFiniteMeasure (volume.restrict (Ω a c).val) := isFiniteMeasure_restrict.mpr (hfinite a c)
  have hfL : MemLp f 2 (volume.restrict (Ω a c).val) :=
    memLp_coordinate_rectangle_piecewise U.property.measurableSet hab hbc u v hu.2.1 hv.2.1
  have hDfL (i : Fin (n + 1)) : MemLp (fun y => Df y i) 2 (volume.restrict (Ω a c).val) :=
    memLp_coordinate_rectangle_piecewise U.property.measurableSet hab hbc _ _ (hu.2.2 i) (hv.2.2 i)
  have hfI : IntegrableOn f (Ω a c).val volume := hfL.integrable (by norm_num)
  have hDfI (i : Fin (n + 1)) : IntegrableOn (fun y => Df y i) (Ω a c).val volume :=
    (hDfL i).integrable (by norm_num)
  have hWeak : HasWeakGradient (Ω a c) f Df := by
    refine ⟨hfI.locallyIntegrableOn, fun i => (hDfI i).locallyIntegrableOn, ?_⟩
    intro i φ hφ hcφ hsφ
    have hφTop (d g : ℝ) : MemLp φ ∞ (volume.restrict (Ω d g).val) :=
      hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
    have hdφTop (d g : ℝ) : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict (Ω d g).val) :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
    have hleftI : IntegrableOn (fun y => coordinateDerivative φ hφ i y • f y) (Ω a c).val :=
      hfI.smul_of_top_right (hdφTop a c)
    have hrightI : IntegrableOn (fun y => φ y • Df y i) (Ω a c).val :=
      (hDfI i).smul_of_top_right (hφTop a c)
    ext j
    have hAu : IntegrableOn (fun y => coordinateDerivative φ hφ i y * (u y) j) (Ω a b).val :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp (hu.2.1.integrable (by norm_num))).smul_of_top_right (hdφTop a b)
    have hAv : IntegrableOn (fun y => coordinateDerivative φ hφ i y * (v y) j) (Ω b c).val :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp (hv.2.1.integrable (by norm_num))).smul_of_top_right (hdφTop b c)
    have hCu : IntegrableOn (fun y => φ y * (Du y i) j) (Ω a b).val :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp ((hu.2.2 i).integrable (by norm_num))).smul_of_top_right (hφTop a b)
    have hCv : IntegrableOn (fun y => φ y * (Dv y i) j) (Ω b c).val :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp ((hv.2.2 i).integrable (by norm_num))).smul_of_top_right (hφTop b c)
    have hleftProj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hleftI
    have hrightProj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hrightI
    change (∫ y in (Ω a c).val, coordinateDerivative φ hφ i y * (f y) j) =
      (∫ y in (Ω a c).val, coordinateDerivative φ hφ i y • f y) j at hleftProj
    change (∫ y in (Ω a c).val, φ y * Df y i j) =
      (∫ y in (Ω a c).val, φ y • Df y i) j at hrightProj
    change (∫ y in (Ω a c).val, coordinateDerivative φ hφ i y • f y) j =
      -(∫ y in (Ω a c).val, φ y • Df y i) j
    rw [← hleftProj, ← hrightProj]
    have hLP (y : Domain (n + 1)) : coordinateDerivative φ hφ i y * (f y) j =
        if T y < b then coordinateDerivative φ hφ i y * (u y) j else coordinateDerivative φ hφ i y * (v y) j := by
      dsimp only [f]
      split_ifs <;> rfl
    have hRP (y : Domain (n + 1)) : φ y * Df y i j =
        if T y < b then φ y * (Du y i) j else φ y * (Dv y i) j := by
      dsimp only [Df]
      split_ifs <;> rfl
    simp_rw [hLP, hRP]
    have hSplitL : (∫ y in (Ω a c).val,
        if T y < b then coordinateDerivative φ hφ i y * (u y) j
          else coordinateDerivative φ hφ i y * (v y) j) =
        (∫ y in (Ω a b).val, coordinateDerivative φ hφ i y * (u y) j) +
          ∫ y in (Ω b c).val, coordinateDerivative φ hφ i y * (v y) j :=
      integral_coordinate_rectangle_piecewise U.property.measurableSet hab hbc _ _ hAu hAv
    have hSplitR : (∫ y in (Ω a c).val,
        if T y < b then φ y * (Du y i) j else φ y * (Dv y i) j) =
        (∫ y in (Ω a b).val, φ y * (Du y i) j) + ∫ y in (Ω b c).val, φ y * (Dv y i) j :=
      integral_coordinate_rectangle_piecewise U.property.measurableSet hab hbc _ _ hCu hCv
    rw [hSplitL, hSplitR]
    exact coordinate_piecewise_weak_test_scalar U hab hbc u v Du Dv hu hv H K hH hK hmatch i j φ hφ hcφ hsφ
  refine ⟨⟨hWeak, hfL, hDfL⟩, ?_, ?_⟩
  · have hpoint (y : Domain (n + 1)) : hsNormSq (Df y) =
        if T y < b then hsNormSq (Du y) else hsNormSq (Dv y) := by
      dsimp only [Df]
      split_ifs <;> rfl
    simp_rw [hpoint]
    exact integral_coordinate_rectangle_piecewise U.property.measurableSet hab hbc _ _
      (integrable_hsNormSq_of_memLp_columns hu.2.2) (integrable_hsNormSq_of_memLp_columns hv.2.2)
  · have hParam (x : Domain n) (t : ℝ) :
        f (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
          if t < b then u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
            else v (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) := by
      have hT : T (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) = t := by
        change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))).2 0 = t
        rw [e.apply_symm_apply]
        simp only [PiLp.single_apply, ite_true]
      dsimp only [f]
      rw [hT]
    simpa only [hParam] using exists_continuous_lp_trace_piecewise (volume.restrict U.val) hab hbc
      (fun p : Domain n × ℝ => u (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      (fun p : Domain n × ℝ => v (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      H K hH hK hmatch

end StratificationTheory
