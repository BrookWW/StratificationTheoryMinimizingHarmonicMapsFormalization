module

public import StratificationTheory.Foundation.GridKernelSampling

/-!
# Native full-plane qualifications before grid selection

An original ambient full-measure event gives one full-measure set of origins
on which every member of a countable family of translated native fibers
retains that event almost everywhere. No postselection predicate is used.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
namespace StratificationTheory

/-- An original ambient a.e. event qualifies almost every entire translated
native kernel fiber. The kernel measure may be any prescribed S-finite one. -/
theorem ae_native_translated_kernel_property {N : ℕ}
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (shift : α → Domain N) (hshift : Measurable shift)
    {P : Domain N → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ᵐ t ∂ν, P (y + shift t) := by
  let T : Domain N × α → Domain N := fun p => p.1 + shift p.2
  have hT : Measure.QuasiMeasurePreserving T
      ((volume : Measure (Domain N)).prod ν) volume :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (hshift.comp measurable_snd))
      (Eventually.of_forall fun t =>
        (measurePreserving_add_right volume (shift t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hT.ae hP)

/-- Original ambient spatial measurability qualifies almost every complete
translated native kernel, including kernels of lower dimension. -/
theorem ae_native_translated_kernel_aestronglyMeasurable {N : ℕ}
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (ν : Measure α) [SFinite ν]
    (shift : α → Domain N) (hshift : Measurable shift)
    {f : Domain N → E} (hf : AEStronglyMeasurable f volume) :
    ∀ᵐ y ∂(volume : Measure (Domain N)),
      AEStronglyMeasurable (fun t => f (y + shift t)) ν := by
  let T : Domain N × α → Domain N := fun p => p.1 + shift p.2
  have hT : Measure.QuasiMeasurePreserving T
      ((volume : Measure (Domain N)).prod ν) volume :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (hshift.comp measurable_snd))
      (Eventually.of_forall fun t =>
        (measurePreserving_add_right volume (shift t)).quasiMeasurePreserving)
  exact (hf.comp_quasiMeasurePreserving hT).prodMk_left

/-- An ambient a.e. property holds along almost every native translated
fiber for almost every origin, for any prescribed measurable fiber shift. -/
theorem ae_native_translated_fiber_property {N k : ℕ}
    (shift : Domain k → Domain N) (hshift : Measurable shift)
    {P : Domain N → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ᵐ t ∂(volume : Measure (Domain k)),
      P (y + shift t) := by
  exact ae_native_translated_kernel_property volume shift hshift hP

/-- All dimensions of a countable prescribed native fiber family qualify on
one ambient full-measure event. The predicate is the original preassigned
ambient event, not an event chosen after a grid offset. -/
theorem ae_native_translated_fiber_family_property
    {N : ℕ} {ι : Type*} [Countable ι] (k : ι → ℕ)
    (shift : ∀ i, Domain (k i) → Domain N) (hshift : ∀ i, Measurable (shift i))
    {P : Domain N → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ i,
      ∀ᵐ t ∂(volume : Measure (Domain (k i))), P (y + shift i t) := by
  exact ae_all_iff.mpr fun i => ae_native_translated_fiber_property (shift i) (hshift i) hP

end StratificationTheory
