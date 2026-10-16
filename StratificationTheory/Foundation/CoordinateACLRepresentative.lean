module

public import StratificationTheory.Foundation.CoordinateLineACL
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Jointly measurable coordinate-line representatives

The representative is the interval mean of the map minus its derivative
primitive, plus that same primitive. All fibers use one literal formula.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

/-- The literal averaged-primitive representative on a family of intervals. -/
@[expose] noncomputable def fiberACLRepresentative {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (u g : α × ℝ → E) (p : α × ℝ) : E :=
  (b - a)⁻¹ • (∫ s in Ioo a b, u (p.1, s) - ∫ r in a..s, g (p.1, r)) +
    ∫ r in a..p.2, g (p.1, r)

/-- A jointly strongly measurable density has a jointly strongly measurable
oriented interval primitive, without an integrability assumption. -/
theorem stronglyMeasurable_fiber_intervalPrimitive {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : α × ℝ → E} (hg : StronglyMeasurable g) (a : ℝ) :
    StronglyMeasurable (fun p : α × ℝ => ∫ r in a..p.2, g (p.1, r)) := by
  let G : (α × ℝ) × ℝ → E := fun p => g (p.1.1, p.2)
  have hG : StronglyMeasurable G := hg.comp_measurable
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hs : MeasurableSet {p : (α × ℝ) × ℝ | a < p.2 ∧ p.2 ≤ p.1.2} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have ht : MeasurableSet {p : (α × ℝ) × ℝ | p.1.2 < p.2 ∧ p.2 ≤ a} :=
    (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hleft := (hG.indicator hs).integral_prod_right' (ν := (volume : Measure ℝ))
  have hright := (hG.indicator ht).integral_prod_right' (ν := (volume : Measure ℝ))
  convert hleft.sub hright using 1
  funext p
  symm
  change (∫ r, ({z : (α × ℝ) × ℝ | a < z.2 ∧ z.2 ≤ z.1.2}.indicator G) (p, r)) -
      (∫ r, ({z : (α × ℝ) × ℝ | z.1.2 < z.2 ∧ z.2 ≤ a}.indicator G) (p, r)) = _
  have h1 : (fun r => ({z : (α × ℝ) × ℝ | a < z.2 ∧ z.2 ≤ z.1.2}.indicator G) (p, r)) =
      (Ioc a p.2).indicator (fun r => g (p.1, r)) := by
    funext r
    rfl
  have h2 : (fun r => ({z : (α × ℝ) × ℝ | z.1.2 < z.2 ∧ z.2 ≤ a}.indicator G) (p, r)) =
      (Ioc p.2 a).indicator (fun r => g (p.1, r)) := by
    funext r
    rfl
  rw [h1, h2, integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rfl

/-- The averaged-primitive formula is strongly measurable for joint strongly
measurable input functions. -/
theorem stronglyMeasurable_fiberACLRepresentative {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u g : α × ℝ → E} (hu : StronglyMeasurable u) (hg : StronglyMeasurable g)
    (a b : ℝ) : StronglyMeasurable (fiberACLRepresentative a b u g) := by
  have hprimitive := stronglyMeasurable_fiber_intervalPrimitive hg a
  have hc := (hu.sub hprimitive).integral_prod_right' (ν := volume.restrict (Ioo a b))
  exact (hc.comp_measurable measurable_fst).const_smul (b - a)⁻¹ |>.add hprimitive

private theorem intervalPrimitive_congr_ae {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b t : ℝ} {f g : ℝ → E}
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) (ht : t ∈ Icc a b) :
    (∫ r in a..t, f r) = ∫ r in a..t, g r := by
  rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  exact hfg.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (Ioo_subset_Ioo_right ht.2)))

private theorem fiberACLRepresentative_congr_fiber {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    {u u' g g' : α × ℝ → E} {x : α}
    (hu : (fun s => u (x, s)) =ᵐ[volume.restrict (Ioo a b)] (fun s => u' (x, s)))
    (hg : (fun s => g (x, s)) =ᵐ[volume.restrict (Ioo a b)] (fun s => g' (x, s)))
    {t : ℝ} (ht : t ∈ Icc a b) :
    fiberACLRepresentative a b u g (x, t) = fiberACLRepresentative a b u' g' (x, t) := by
  have hmean : (∫ s in Ioo a b, u (x, s) - ∫ r in a..s, g (x, r)) =
      ∫ s in Ioo a b, u' (x, s) - ∫ r in a..s, g' (x, r) := by
    apply integral_congr_ae
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    rw [hs, intervalPrimitive_congr_ae hg ⟨hsI.1.le, hsI.2.le⟩]
  simp only [fiberACLRepresentative, hmean, intervalPrimitive_congr_ae hg ht]

/-- Joint a.e. input data give joint a.e. measurability of the literal
representative on the entire closed time interval. -/
theorem aestronglyMeasurable_fiberACLRepresentative {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [SigmaFinite μ] {a b : ℝ} {u g : α × ℝ → E}
    (hu : AEStronglyMeasurable u (μ.prod (volume.restrict (Ioo a b))))
    (hg : AEStronglyMeasurable g (μ.prod (volume.restrict (Ioo a b)))) :
    AEStronglyMeasurable (fiberACLRepresentative a b u g)
      (μ.prod (volume.restrict (Icc a b))) := by
  have hbase : ∀ᵐ x ∂μ,
      (fun s => u (x, s)) =ᵐ[volume.restrict (Ioo a b)] (fun s => hu.mk u (x, s)) ∧
      (fun s => g (x, s)) =ᵐ[volume.restrict (Ioo a b)] (fun s => hg.mk g (x, s)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hu.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with x hxU hxG
    exact ⟨hxU, hxG⟩
  have heq : fiberACLRepresentative a b u g =ᵐ[μ.prod (volume.restrict (Icc a b))]
      fiberACLRepresentative a b (hu.mk u) (hg.mk g) := by
    have hb := (Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := volume.restrict (Icc a b))).ae hbase
    have ht := (Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := volume.restrict (Icc a b))).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hb, ht] with p hp hpt
    exact fiberACLRepresentative_congr_fiber hp.1 hp.2 hpt
  exact (stronglyMeasurable_fiberACLRepresentative hu.stronglyMeasurable_mk
    hg.stronglyMeasurable_mk a b).aestronglyMeasurable.congr heq.symm

private theorem fiberACLRepresentative_eq_of_integral_increments {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b)
    {u g : α × ℝ → E} {x : α} {F : ℝ → E}
    (hF : F =ᵐ[volume.restrict (Ioo a b)] (fun t => u (x, t)))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ r in s..t, g (x, r)) :
    ∀ t ∈ Icc a b, fiberACLRepresentative a b u g (x, t) = F t := by
  have haa : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hprimitive (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ r in a..t, g (x, r)) = F t - F a := (hinc a haa t ht).symm
  have hmean : (∫ s in Ioo a b, u (x, s) - ∫ r in a..s, g (x, r)) =
      (b - a) • F a := by
    have heq : (fun s => u (x, s) - ∫ r in a..s, g (x, r)) =ᵐ[
        volume.restrict (Ioo a b)] (fun _ => F a) := by
      filter_upwards [hF, ae_restrict_mem measurableSet_Ioo] with s hs hsI
      rw [← hs, hprimitive s ⟨hsI.1.le, hsI.2.le⟩]
      exact sub_sub_cancel _ _
    rw [integral_congr_ae heq, integral_const, Measure.real,
      Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
  intro t ht
  rw [fiberACLRepresentative, hmean, hprimitive t ht, smul_smul,
    inv_mul_cancel₀ (sub_pos.mpr hab).ne', one_smul]
  exact add_sub_cancel _ _

private theorem ae_eq_of_ae_ae_eq {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SigmaFinite μ] [SigmaFinite ν] [NormedAddCommGroup E]
    {f g : α × β → E} (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = g (x, y)) :
    f =ᵐ[μ.prod ν] g := by
  have hset : MeasurableSet {x | hf.mk f x = hg.mk g x} := by
    have hm := measurableSet_eq_fun
      (hf.stronglyMeasurable_mk.sub hg.stronglyMeasurable_mk).norm.measurable
      (measurable_const (a := (0 : ℝ)))
    simpa only [Pi.sub_apply, norm_eq_zero, sub_eq_zero] using hm
  have hm : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk, h] with x hfx hgx hx
    filter_upwards [hfx, hgx, hx] with y hfy hgy hxy
    exact hfy.symm.trans (hxy.trans hgy)
  exact hf.ae_eq_mk.trans (hm.trans hg.ae_eq_mk.symm)

/-- Actual Sobolev data produce one joint measurable averaged-primitive
representative. Almost every closed coordinate line is absolutely continuous,
and its increments integrate the original weak-gradient column. -/
theorem coordinateACLRepresentative_of_memW12_ball {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U : Domain n × ℝ → Ambient q := fun p =>
      u (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
    let G : Domain n × ℝ → Ambient q := fun p =>
      Du (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) (Fin.natAdd n (0 : Fin 1))
    let F := fiberACLRepresentative a b U G
    AEStronglyMeasurable F
      ((volume.restrict S).prod (volume.restrict (Icc a b))) ∧
    F =ᵐ[(volume.restrict S).prod (volume.restrict (Ioo a b))] U ∧
    ∀ᵐ x ∂volume.restrict S,
      AbsolutelyContinuousOnInterval (fun t => F (x, t)) a b ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        F (x, t) - F (x, s) = ∫ r in s..t, G (x, r) := by
  intro e U G F
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
  have hU : MemLp U 2 (μ.prod ν) :=
    (hu.2.1.mono_measure hμmono).comp_measurePreserving hm
  have hG : MemLp G 2 (μ.prod ν) :=
    ((hu.2.2 (Fin.natAdd n (0 : Fin 1))).mono_measure hμmono).comp_measurePreserving hm
  have hF : AEStronglyMeasurable F (μ.prod (volume.restrict (Icc a b))) :=
    aestronglyMeasurable_fiberACLRepresentative hU.aestronglyMeasurable hG.aestronglyMeasurable
  have hlines := ae_coordinateLine_exists_ac_of_memW12_ball hR hu hS hab hrect
  have hFline : ∀ᵐ x ∂μ,
      AbsolutelyContinuousOnInterval (fun t => F (x, t)) a b ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F (x, t) - F (x, s) = ∫ r in s..t, G (x, r)) ∧
      (fun t => F (x, t)) =ᵐ[ν] (fun t => U (x, t)) := by
    filter_upwards [hlines] with x hx
    obtain ⟨H, hHac, hHae, hHinc⟩ := hx.2.2
    have hEq := fiberACLRepresentative_eq_of_integral_increments hab
      (u := U) (g := G) hHae hHinc
    have hac : AbsolutelyContinuousOnInterval (fun t => ∫ r in a..t, G (x, r)) a b :=
      intervalPrimitive_absolutelyContinuous_of_memLp_two hab.le hx.2.1
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ =>
        (b - a)⁻¹ • ∫ s in Ioo a b, U (x, s) - ∫ r in a..s, G (x, r)) a b :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    refine ⟨hc.add hac, ?_, ?_⟩
    · intro s hs t ht
      change (_ + ∫ r in a..t, G (x, r)) - (_ + ∫ r in a..s, G (x, r)) = _
      rw [add_sub_add_left_eq_sub]
      exact intervalPrimitive_sub hab.le hx.2.1 hs ht
    · filter_upwards [hHae, ae_restrict_mem measurableSet_Ioo] with t ht htI
      exact (hEq t ⟨htI.1.le, htI.2.le⟩).trans ht
  refine ⟨hF, ?_, hFline.mono fun _ hx => ⟨hx.1, hx.2.1⟩⟩
  apply ae_eq_of_ae_ae_eq
    (hF.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono_set volume Ioo_subset_Icc_self))) hU.aestronglyMeasurable
  exact hFline.mono fun _ hx => hx.2.2

end StratificationTheory
