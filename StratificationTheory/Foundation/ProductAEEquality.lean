module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Product almost-everywhere equality from measurable sections

Almost-everywhere strongly measurable functions admit a joint equality from
iterated equality of their sections. This joint equality permits reversal of
the almost-everywhere quantifiers without asserting pointwise raw equality.
-/

public section
open MeasureTheory Filter TopologicalSpace
namespace StratificationTheory

theorem ae_eq_of_ae_ae_of_aestronglyMeasurable
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace E] [MetrizableSpace E]
    {μ : Measure X} {ν : Measure Y} [SFinite ν]
    {f g : X × Y → E}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (hfg : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = g (x, y)) :
    f =ᵐ[μ.prod ν] g := by
  have hfm := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hgm := Measure.ae_ae_of_ae_prod hg.ae_eq_mk
  have hmk : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, hf.mk f (x, y) = hg.mk g (x, y) := by
    filter_upwards [hfg, hfm, hgm] with x hx hfx hgx
    filter_upwards [hx, hfx, hgx] with y hxy hfxy hgxy
    exact hfxy.symm.trans (hxy.trans hgxy)
  have hprod : hf.mk f =ᵐ[μ.prod ν] hg.mk g :=
    (Measure.ae_prod_iff_ae_ae (hf.stronglyMeasurable_mk.measurableSet_eq_fun
      hg.stronglyMeasurable_mk)).mpr hmk
  exact hf.ae_eq_mk.trans (hprod.trans hg.ae_eq_mk.symm)

theorem ae_ae_eq_swap_of_aestronglyMeasurable
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace E] [MetrizableSpace E]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f g : X × Y → E}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (hfg : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = g (x, y)) :
    ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) = g (x, y) := by
  have hprod := ae_eq_of_ae_ae_of_aestronglyMeasurable hf hg hfg
  exact Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod)

end StratificationTheory
