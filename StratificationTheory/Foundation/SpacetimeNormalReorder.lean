module

public import StratificationTheory.Foundation.CubicalAdjacentConeSwap
public import StratificationTheory.Foundation.CylinderCoordinateMeasure

/-!
# Native spatial-normal coordinates with independent time

The genuine finite coordinate swap puts the spatial normal variable before
the original time variable. Its exact native measure transport supplies
joint measurability from the original spatial-time L2 map.
-/

public section
open HarmonicMaps MeasureTheory Set
namespace StratificationTheory

theorem spacetime_normal_reorder_coordinates (n : ℕ)
    (x : Domain n) (τ η : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let A := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    A (E.symm (e.symm (x,EuclideanSpace.single (0 : Fin 1) τ),
      EuclideanSpace.single (0 : Fin 1) η)) =
      E.symm (e.symm (x,EuclideanSpace.single (0 : Fin 1) η),EuclideanSpace.single (0 : Fin 1) τ) := by
  intro e E A
  apply E.injective
  have hSwap : ∀ z : Domain (n + 1 + 1), E (A z) =
      (e.symm ((e (E z).1).1,EuclideanSpace.single (0 : Fin 1) ((E z).2 0)),
        EuclideanSpace.single (0 : Fin 1) ((e (E z).1).2 0)) :=
    (cubical_adjacent_cone_swap_coordinates n).1
  rw [hSwap,E.apply_symm_apply,E.apply_symm_apply,e.apply_symm_apply]
  simp only [PiLp.single_apply,ite_true]

theorem measurePreserving_spacetime_normal_reorder {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S)
    {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Ω := {z : Domain (n + 1 + 1) |
      ((e (E z).1).1 ∈ S ∧ (e (E z).1).2 0 ∈ J) ∧ (E z).2 0 ∈ I}
    let R := fun p : (Domain n × ℝ) × ℝ =>
      E.symm (e.symm (p.1.1,EuclideanSpace.single (0 : Fin 1) p.2),EuclideanSpace.single (0 : Fin 1) p.1.2)
    MeasurePreserving R (((volume.restrict S).prod (volume.restrict I)).prod (volume.restrict J))
      (volume.restrict Ω) := by
  intro e E Ω R
  let r := fun p : Domain n × ℝ => e.symm (p.1,EuclideanSpace.single (0 : Fin 1) p.2)
  let rE := fun p : Domain (n + 1) × ℝ => E.symm (p.1,EuclideanSpace.single (0 : Fin 1) p.2)
  let A := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
  have hFull := A.measurePreserving.comp ((measurePreserving_cylinder_coordinates_inverse (n + 1)).comp
    ((measurePreserving_cylinder_coordinates_inverse n).prod
      (MeasurePreserving.id (volume : Measure ℝ))))
  have hFunction : (A ∘ rE ∘ Prod.map r id) = R := by
    funext p
    exact spacetime_normal_reorder_coordinates n p.1.1 p.1.2 p.2
  change MeasurePreserving (A ∘ rE ∘ Prod.map r id)
    (((volume : Measure (Domain n)).prod volume).prod volume) volume at hFull
  rw [hFunction] at hFull
  have hΩ : MeasurableSet Ω := by
    apply ((hS.preimage ?_).inter (hJ.preimage ?_)).inter (hI.preimage ?_)
    all_goals fun_prop
  have hPre : R ⁻¹' Ω = (S ×ˢ I) ×ˢ J := by
    ext p
    simp only [R,Ω,mem_preimage,mem_setOf_eq,E.apply_symm_apply,e.apply_symm_apply,
      PiLp.single_apply,ite_true,mem_prod]
    tauto
  have h := hFull.restrict_preimage hΩ
  rw [hPre,← Measure.prod_restrict,← Measure.prod_restrict] at h
  exact h

/-- Original spatial-time L2 data give the actual jointly measurable
original spatial-normal slices in the native product carrier. -/
theorem memLp_spacetime_normal_reorder {n : ℕ} {E₀ : Type*} [NormedAddCommGroup E₀]
    {S : Set (Domain n)} (hS : MeasurableSet S)
    {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (u : Domain (n + 1 + 1) → E₀) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Ω := {z : Domain (n + 1 + 1) |
      ((e (E z).1).1 ∈ S ∧ (e (E z).1).2 0 ∈ J) ∧ (E z).2 0 ∈ I}
    MemLp u 2 (volume.restrict Ω) →
      MemLp (fun p : (Domain n × ℝ) × ℝ => u
        (E.symm (e.symm (p.1.1,EuclideanSpace.single (0 : Fin 1) p.2),
          EuclideanSpace.single (0 : Fin 1) p.1.2)))
        2 (((volume.restrict S).prod (volume.restrict I)).prod (volume.restrict J)) := by
  intro e E Ω hu
  exact hu.comp_measurePreserving (measurePreserving_spacetime_normal_reorder hS hI hJ)

end StratificationTheory
