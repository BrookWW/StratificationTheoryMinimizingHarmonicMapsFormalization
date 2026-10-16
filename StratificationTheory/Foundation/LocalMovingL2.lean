module

public import HarmonicMaps.Analysis.L2TranslationContinuity
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Local L2 limits under moving translations

Small translations preserve original local L2 convergence on compact
subsets of the original open set. Compact containment supplies the actual
range inclusion, and zero extensions are used only inside the proof.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Original local L2 errors still tend to zero under small translations
on every compact subset of the original open domain. -/
theorem tendsto_local_L2_after_small_translation {ι E : Type*} {l : Filter ι}
    [NormedAddCommGroup E] {n : ℕ} {Ω : Set (Domain n)} (hΩ : IsOpen Ω)
    {K : Set (Domain n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {f : ι → Domain n → E} {g : Domain n → E}
    (hg : MemLp g 2 (volume.restrict Ω))
    (hf : ∀ᶠ i in l, MemLp (fun x => f i x - g x) 2 (volume.restrict Ω))
    (hlim : Tendsto (fun i => eLpNorm (fun x => f i x - g x) 2 (volume.restrict Ω)) l (𝓝 0))
    {h : ι → Domain n} (hh : Tendsto h l (𝓝 0)) :
    (∀ᶠ i in l, (∀ x ∈ K, x + h i ∈ Ω) ∧
      MemLp (fun x => f i (x + h i) - g x) 2 (volume.restrict K)) ∧
    Tendsto (fun i => eLpNorm (fun x => f i (x + h i) - g x) 2 (volume.restrict K)) l (𝓝 0) := by
  let G : Domain n → E := Ω.indicator g
  let F : ι → Domain n → E := fun i => Ω.indicator (fun x => f i x - g x)
  have hG : MemLp G 2 volume := memLp_zeroExtension hΩ.measurableSet hg
  have hF : ∀ᶠ i in l, MemLp (F i) 2 volume :=
    hf.mono fun _ hi => memLp_zeroExtension hΩ.measurableSet hi
  have hgeometry : ∀ᶠ i in l, ∀ x ∈ K, x + h i ∈ Ω := by
    obtain ⟨d, hd, hthick⟩ := hK.exists_thickening_subset_open hΩ hKΩ
    have hsmall : ∀ᶠ i in l, ‖h i‖ < d := by
      have ht : Tendsto (fun i => ‖h i‖) l (𝓝 0) := by simpa only [norm_zero] using hh.norm
      exact ht.eventually (eventually_lt_nhds hd)
    filter_upwards [hsmall] with i hi x hx
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    simpa only [dist_eq_norm, add_sub_cancel_left] using hi
  have hGshift (i : ι) : MemLp (fun x => G (x + h i)) 2 volume :=
    hG.comp_measurePreserving (measurePreserving_add_right volume (h i))
  have hGlim : Tendsto (fun i => eLpNorm (fun x => G (x + h i) - G x) 2 volume) l (𝓝 0) := by
    have hneg : Tendsto (fun i => -h i) l (𝓝 0) := by simpa only [neg_zero] using hh.neg
    simpa only [Function.comp_def, sub_neg_eq_add] using
      (tendsto_eLpNorm_translation_sub hG).comp hneg
  have hdata : ∀ᶠ i in l,
      MemLp (fun x => f i (x + h i) - g x) 2 (volume.restrict K) ∧
      eLpNorm (fun x => f i (x + h i) - g x) 2 (volume.restrict K) ≤
        eLpNorm (fun x => f i x - g x) 2 (volume.restrict Ω) +
          eLpNorm (fun x => G (x + h i) - G x) 2 volume := by
    filter_upwards [hF, hgeometry] with i hi hinside
    have hFL : MemLp (fun x => F i (x + h i)) 2 volume :=
      hi.comp_measurePreserving (measurePreserving_add_right volume (h i))
    have hGL : MemLp (fun x => G (x + h i) - G x) 2 volume := (hGshift i).sub hG
    let A : Domain n → E := fun x => F i (x + h i) + (G (x + h i) - G x)
    have hA : MemLp A 2 volume := hFL.add hGL
    have hEq : A =ᵐ[volume.restrict K] (fun x => f i (x + h i) - g x) := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      dsimp only [A, F, G]
      rw [Set.indicator_of_mem (hinside x hx), Set.indicator_of_mem (hinside x hx),
        Set.indicator_of_mem (hKΩ hx)]
      abel
    refine ⟨(hA.mono_measure Measure.restrict_le_self).ae_eq hEq, ?_⟩
    calc
      _ = eLpNorm A 2 (volume.restrict K) := (eLpNorm_congr_ae hEq).symm
      _ ≤ eLpNorm A 2 volume := eLpNorm_mono_measure A Measure.restrict_le_self
      _ ≤ eLpNorm (fun x => F i (x + h i)) 2 volume +
          eLpNorm (fun x => G (x + h i) - G x) 2 volume :=
        eLpNorm_add_le hFL.aestronglyMeasurable hGL.aestronglyMeasurable (by norm_num)
      _ = _ := by
        have hnorm : eLpNorm (fun x => F i (x + h i)) 2 volume = eLpNorm (F i) 2 volume :=
          eLpNorm_comp_measurePreserving (g := F i) (f := fun x : Domain n => x + h i)
            (μ := (volume : Measure (Domain n))) (ν := (volume : Measure (Domain n)))
            (p := (2 : ℝ≥0∞)) hi.aestronglyMeasurable
            (measurePreserving_add_right volume (h i))
        rw [hnorm]
        change eLpNorm (Ω.indicator (fun x => f i x - g x)) 2 volume + _ = _
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩ.measurableSet]
  refine ⟨?_, ?_⟩
  · filter_upwards [hgeometry, hdata] with i hgeom hi
    exact ⟨hgeom, hi.1⟩
  · have hupper := hlim.add hGlim
    have hupper' : Tendsto (fun i =>
        eLpNorm (fun x => f i x - g x) 2 (volume.restrict Ω) +
          eLpNorm (fun x => G (x + h i) - G x) 2 volume) l (𝓝 0) := by
      simpa only [zero_add] using hupper
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper'
      (Eventually.of_forall fun _ => zero_le) (hdata.mono fun _ hi => hi.2)

end StratificationTheory
