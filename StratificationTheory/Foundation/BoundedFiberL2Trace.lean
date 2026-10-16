module

public import StratificationTheory.Foundation.RadialTraceCompatibility
public import HarmonicMaps.Analysis.VariableMollificationL2
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IsLUB

/-!
# Native L2 traces of bounded continuous line representatives

Almost-everywhere continuity of bounded line representatives gives continuous
native L2 classes on a finite base. Interior slice measurability suffices:
every closed-interval slice is obtained as an almost-everywhere limit of
measurable interior slices. The same original endpoint classes are retained.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Uniformly bounded almost-everywhere convergence on a finite measure space
gives convergence in the actual native L2 difference seminorm. -/
theorem tendsto_eLpNorm_two_sub_zero_of_ae_bounded
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → α → E} {g : α → E} {M : ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hg : AEStronglyMeasurable g μ)
    (hfb : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ M) (hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ M)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    Tendsto (fun i => eLpNorm (fun x => f i x - g x) 2 μ) l (𝓝 0) := by
  have hmem (i : ι) : MemLp (fun x => f i x - g x) 2 μ :=
    (MemLp.of_bound (hf i) M (hfb i)).sub (MemLp.of_bound hg M hgb)
  have hsq : Tendsto (fun i => ∫ x, ‖f i x - g x‖ ^ 2 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (F := fun i x => ‖f i x - g x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ => (2 * M) ^ 2)
      (Eventually.of_forall fun i => ((hf i).sub hg).norm.pow 2)
      (Eventually.of_forall fun i => by
        filter_upwards [hfb i, hgb] with x hfx hgx
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hnorm : ‖f i x - g x‖ ≤ 2 * M :=
          (norm_sub_le _ _).trans (by linarith only [hfx, hgx])
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
      (integrable_const _)
      (hlim.mono fun x hx => by
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
          (hx.sub_const (g x)).norm.pow 2)
    simpa only [integral_zero] using h
  have hnorm (i : ι) : eLpNorm (fun x => f i x - g x) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, ‖f i x - g x‖ ^ 2 ∂μ)) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using
      (hmem i).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have ht := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  simpa only [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero, ← hnorm] using ht

private theorem exists_seq_interior_of_ae {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Icc a b) {P : ℝ → Prop}
    (hP : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b, P t) :
    ∃ τ : ℕ → ℝ, (∀ j, τ j ∈ Ioo a b ∧ P (τ j)) ∧
      Tendsto τ atTop (𝓝 c) := by
  have hdense := (volume : Measure ℝ).dense_of_ae hP
  by_cases hca : c = a
  · subst c
    obtain ⟨τ, _hτmono, hτ, hlim⟩ := hdense.exists_seq_strictAnti_tendsto_of_lt hab
    exact ⟨τ, fun j => ⟨(hτ j).1, (hτ j).2 (hτ j).1⟩, hlim⟩
  · have hac : a < c := lt_of_le_of_ne hc.1 (Ne.symm hca)
    obtain ⟨τ, _hτmono, hτ, hlim⟩ := hdense.exists_seq_strictMono_tendsto_of_lt hac
    refine ⟨τ, ?_, hlim⟩
    intro j
    have hI : τ j ∈ Ioo a b := ⟨(hτ j).1.1, (hτ j).1.2.trans_le hc.2⟩
    exact ⟨hI, (hτ j).2 hI⟩

/-- Bounded original line representatives continuous almost everywhere on a
closed interval determine one continuous native L2 curve. Every value,
including both endpoint values, is the class of that same raw line slice.
Only almost-everywhere interior spatial measurability is needed. -/
theorem exists_continuous_L2_trace_of_bounded_fiber_continuity
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) {f : α × ℝ → E} {M : ℝ}
    (hmeas : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      AEStronglyMeasurable (fun x => f (x, t)) μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun t => f (x, t)) (Icc a b))
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ Icc a b, ‖f (x, t)‖ ≤ M) :
    ∃ H : C(Icc a b, Lp E 2 μ),
      (∀ t : Icc a b, ∃ hslice : MemLp (fun x => f (x, t.val)) 2 μ,
        H t = hslice.toLp (fun x => f (x, t.val))) ∧
      ∀ K : C(Icc a b, Lp E 2 μ),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
            K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) → K = H := by
  have hmeasAll (t : Icc a b) : AEStronglyMeasurable (fun x => f (x, t.val)) μ := by
    obtain ⟨τ, hτ, hτlim⟩ := exists_seq_interior_of_ae hab t.property hmeas
    have hτwithin : Tendsto τ atTop (𝓝[Icc a b] t.val) :=
      tendsto_nhdsWithin_iff.mpr ⟨hτlim, Eventually.of_forall fun j =>
        ⟨(hτ j).1.1.le, (hτ j).1.2.le⟩⟩
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun j => (hτ j).2)
      (hcont.mono fun x hx => (hx t.val t.property).tendsto.comp hτwithin)
  have hmem (t : Icc a b) : MemLp (fun x => f (x, t.val)) 2 μ :=
    MemLp.of_bound (hmeasAll t) M (hbound.mono fun _ hx => hx t.val t.property)
  let Hfun : Icc a b → Lp E 2 μ := fun t => (hmem t).toLp (fun x => f (x, t.val))
  have hHcont : Continuous Hfun := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun t : Icc a b => fun x => f (x, t.val)) hmem
      (fun x => f (x, t₀.val)) (hmem t₀)).mpr
    exact tendsto_eLpNorm_two_sub_zero_of_ae_bounded hmeasAll (hmeasAll t₀)
      (fun t => hbound.mono fun _ hx => hx t.val t.property)
      (hbound.mono fun _ hx => hx t₀.val t₀.property)
      (hcont.mono fun x hx => hx.restrict.tendsto t₀)
  let H : C(Icc a b, Lp E 2 μ) := ⟨Hfun, hHcont⟩
  refine ⟨H, fun t => ⟨hmem t, rfl⟩, ?_⟩
  intro K hK
  apply continuous_Lp_representatives_eq_of_ae_slices hab K H hK
    (Eventually.of_forall fun t ht => ⟨hmem ⟨t, ht.1.le, ht.2.le⟩, rfl⟩)
  exact Eventually.of_forall fun _ _ => Filter.EventuallyEq.rfl

/-- A bounded continuous line representative identifies the original raw cut
class at any chosen cut where raw recovery holds on the whole base almost
everywhere. No endpoint equality with a canonical trace is assumed. -/
theorem continuous_L2_trace_value_of_bounded_line_representative
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) {f F : α × ℝ → E} {M : ℝ}
    (H : C(Icc a b, Lp E 2 μ))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t)))
    (hFae : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      (fun x => F (x, t)) =ᵐ[μ] (fun x => f (x, t)))
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun t => F (x, t)) (Icc a b))
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ Icc a b, ‖F (x, t)‖ ≤ M)
    (c : Icc a b) (hcut : (fun x => F (x, c.val)) =ᵐ[μ] (fun x => f (x, c.val))) :
    ∃ hslice : MemLp (fun x => f (x, c.val)) 2 μ,
      H c = hslice.toLp (fun x => f (x, c.val)) := by
  have hmeas : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo a b,
      AEStronglyMeasurable (fun x => F (x, t)) μ := by
    filter_upwards [hH, hFae] with t ht hFt htI
    obtain ⟨hft, _⟩ := ht htI
    exact hft.aestronglyMeasurable.congr (hFt htI).symm
  obtain ⟨K, hK, _hunique⟩ :=
    exists_continuous_L2_trace_of_bounded_fiber_continuity μ hab hmeas hcont hbound
  have hHK : H = K := continuous_Lp_representatives_eq_of_ae_slices hab H K hH
    (Eventually.of_forall fun t ht => hK ⟨t, ht.1.le, ht.2.le⟩)
    (hFae.mono fun _ ht htI => (ht htI).symm)
  obtain ⟨hFc, hKc⟩ := hK c
  have hfc := hFc.ae_eq hcut
  refine ⟨hfc, ?_⟩
  rw [hHK, hKc]
  exact hFc.toLp_congr hfc hcut

end StratificationTheory
