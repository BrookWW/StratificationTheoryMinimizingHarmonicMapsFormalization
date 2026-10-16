module

public import StratificationTheory.Foundation.CubicalConeMeasureTransport
public import StratificationTheory.Foundation.CylinderCoordinateMeasure

/-!
# Native Euclidean face-cone coordinates

The Euclidean spatial-time split transfers the positive-cone Jacobian and
original native product a.e. classes to the ambient Euclidean cone.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

private theorem cone_lintegral_comp_of_aemeasurable {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {μ : Measure A} {ν : Measure B}
    {f : B → ℝ≥0∞} {P : A → B} (hP : MeasurePreserving P μ ν)
    (hf : AEMeasurable f ν) : (∫⁻ x, f (P x) ∂μ) = ∫⁻ y, f y ∂ν := by
  calc
    _ = ∫⁻ x, hf.mk f (P x) ∂μ :=
      lintegral_congr_ae (hP.quasiMeasurePreserving.ae hf.ae_eq_mk)
    _ = ∫⁻ y, hf.mk f y ∂ν := hP.lintegral_comp hf.measurable_mk
    _ = _ := (lintegral_congr_ae hf.ae_eq_mk).symm

/-- The literal Euclidean positive cone over an arbitrary measurable face
has the exact native t^n volume formula in face-time coordinates. -/
theorem lintegral_native_positive_cone {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ((e y).2 0)⁻¹ • (e y).1 ∈ S}
    ∀ {f : Domain (n + 1) → ℝ≥0∞}, AEMeasurable f (volume.restrict C) →
      (∫⁻ y in C, f y) =
        ∫⁻ t in J, ENNReal.ofReal (t ^ n) * ∫⁻ x in S,
          f (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) := by
  intro e C f hf
  let P : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  let V := {p : Domain n × ℝ | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S}
  have hV : MeasurableSet V :=
    (hJ.preimage measurable_snd).inter (hS.preimage (measurable_snd.inv.smul measurable_fst))
  have hC : MeasurableSet C := hV.preimage (measurePreserving_cylinder_coordinates n).measurable
  have hMP := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hC
  have hpre : P ⁻¹' C = V := by
    ext p
    simp only [P, C, V, mem_preimage, mem_setOf_eq, e.apply_symm_apply,
      PiLp.single_apply, ite_true]
  change MeasurePreserving P (((volume : Measure (Domain n)).prod volume).restrict
    (P ⁻¹' C)) (volume.restrict C) at hMP
  rw [hpre] at hMP
  have hfm : AEMeasurable (f ∘ P)
      (((volume : Measure (Domain n)).prod volume).restrict V) :=
    hf.comp_quasiMeasurePreserving hMP.quasiMeasurePreserving
  have hJac := lintegral_product_positive_cone hS hJ hJpos hfm
  have hEq := cone_lintegral_comp_of_aemeasurable hMP hf
  exact hEq.symm.trans hJac

/-- Literal inverse Euclidean face-cone coordinates preserve native a.e.
classes from the original face-time product measure. -/
theorem quasiMeasurePreserving_native_inverse_positive_cone {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ((e y).2 0)⁻¹ • (e y).1 ∈ S}
    Measure.QuasiMeasurePreserving
      (fun y : Domain (n + 1) => (((e y).2 0)⁻¹ • (e y).1, (e y).2 0))
      (volume.restrict C) ((volume.restrict S).prod (volume.restrict J)) := by
  intro e C
  let V := {p : Domain n × ℝ | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S}
  have hV : MeasurableSet V :=
    (hJ.preimage measurable_snd).inter (hS.preimage (measurable_snd.inv.smul measurable_fst))
  have hMP := (measurePreserving_cylinder_coordinates n).restrict_preimage hV
  have hpre : (fun y : Domain (n + 1) => ((e y).1, (e y).2 0)) ⁻¹' V = C := rfl
  change MeasurePreserving (fun y : Domain (n + 1) => ((e y).1, (e y).2 0))
    (volume.restrict ((fun y : Domain (n + 1) => ((e y).1, (e y).2 0)) ⁻¹' V))
    (((volume : Measure (Domain n)).prod volume).restrict V) at hMP
  rw [hpre] at hMP
  exact (quasiMeasurePreserving_inverse_positive_cone hS hJ hJpos).comp hMP.quasiMeasurePreserving

end StratificationTheory
