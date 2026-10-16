module

public import StratificationTheory.Foundation.SpacetimeNormalReorder
public import StratificationTheory.Foundation.CubicalConeGeometry

/-!
# Original unit-face spatial normal slices in native time products

The actual coordinate split identifies the full original unit-face carrier.
Its native spatial-time L2 map supplies jointly measurable original normal
slices with the independent time measure unchanged.
-/

public section
open HarmonicMaps MeasureTheory Set
namespace StratificationTheory

theorem mem_unit_coordinate_face_split_iff {n : ℕ} (x : Domain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    x ∈ (⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) ↔
      (e x).1 ∈ (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) ∧
      (e x).2 0 ∈ Ioo (-1 : ℝ) 1 := by
  intro e
  rw [mem_unit_coordinate_face_iff,mem_unit_coordinate_face_iff]
  constructor
  · intro h
    exact ⟨fun i => h i.castSucc,abs_lt.mp (h (Fin.last n))⟩
  · intro h i
    refine Fin.addCases (fun j : Fin n => h.1 j) (fun j : Fin 1 => ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact abs_lt.mpr h.2

theorem memLp_unit_cube_spacetime_normal_slices {n : ℕ} {E₀ : Type*} [NormedAddCommGroup E₀]
    (u : Domain (n + 1 + 1) → E₀) (ε : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let B := ⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω := {z : Domain (n + 1 + 1) | (E z).1 ∈ B ∧ (E z).2 0 ∈ Ioo (0 : ℝ) ε}
    MemLp u 2 (volume.restrict Ω) →
      MemLp (fun p : (Domain n × ℝ) × ℝ => u
        (E.symm (e.symm (p.1.1,EuclideanSpace.single (0 : Fin 1) p.2),
          EuclideanSpace.single (0 : Fin 1) p.1.2)))
        2 (((volume.restrict S).prod (volume.restrict (Ioo (0 : ℝ) ε))).prod
          (volume.restrict (Ioo (-1 : ℝ) 1))) := by
  intro e E S B Ω hu
  have hSource : {z : Domain (n + 1 + 1) |
      ((e (E z).1).1 ∈ S ∧ (e (E z).1).2 0 ∈ Ioo (-1 : ℝ) 1) ∧
        (E z).2 0 ∈ Ioo (0 : ℝ) ε} = Ω := by
    ext z
    exact and_congr (mem_unit_coordinate_face_split_iff (E z).1).symm Iff.rfl
  have hSmall : MeasurableSet S := (isOpen_iInter_of_finite fun i : Fin n =>
    isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous).measurableSet
  apply memLp_spacetime_normal_reorder hSmall measurableSet_Ioo measurableSet_Ioo u
  rwa [hSource]

end StratificationTheory
