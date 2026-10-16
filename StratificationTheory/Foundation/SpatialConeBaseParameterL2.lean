module

public import StratificationTheory.Foundation.SpatialConeTimeProductDomination
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Original base classes on a spatial cone with unchanged time

An original native base class extends along the actual spatial rays while
retaining an independent parameter. Bounded positive heights give genuine
L2 for that same literal pullback.
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped ENNReal
namespace StratificationTheory

theorem memLp_spatial_cone_base_independent_parameter {n : ℕ} {A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E]
    (τ : Measure A) [SFinite τ]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    [IsFiniteMeasure ((volume : Measure ℝ).restrict J)]
    (hJpos : ∀ t ∈ J, 0 < t) {M : ℝ} (hJM : ∀ t ∈ J, t ≤ M)
    (g : Domain n × A → E) (hg : MemLp g 2 ((volume.restrict S).prod τ)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ J ∧ ξ y ∈ S}
    MemLp (fun p : Domain (n + 1) × A => g (ξ p.1,p.2)) 2 ((volume.restrict C).prod τ) := by
  intro e T ξ C
  let Q : Domain (n + 1) × A → (Domain n × A) × ℝ := fun p => ((ξ p.1,p.2),T p.1)
  have hT : Measurable T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hξ : Measurable ξ := hT.inv.smul (measurable_fst.comp e.continuous.measurable)
  have hQ : Measurable Q :=
    ((hξ.comp measurable_fst).prodMk measurable_snd).prodMk (hT.comp measurable_fst)
  have hdom := map_native_inverse_cone_independent_parameter_le_smul τ hS hJ hJpos hJM
  exact memLp_comp_of_map_le_smul hQ.aemeasurable ENNReal.ofReal_ne_top hdom
    (hg.comp_fst ((volume : Measure ℝ).restrict J))

end StratificationTheory
