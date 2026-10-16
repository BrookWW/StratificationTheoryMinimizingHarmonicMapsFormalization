module

public import StratificationTheory.Foundation.CubicalSignedConeCover
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

/-!
# Actual finite spatial annular cone partition with independent time

The original signed spatial cones give disjoint open spatial-time pieces
and cover the fixed annular slab up to native ambient volume zero. Time is
absent from the dominance comparisons.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
namespace StratificationTheory

theorem isOpen_spatial_annular_slab (n : ℕ) (ε : ℝ) :
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    IsOpen {y : Domain (n + 1 + 1) | ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1 ∧
      (E y).2 0 ∈ Ioo (0 : ℝ) ε} := by
  intro E
  exact (isOpen_Ioo.preimage (continuous_fst.comp E.continuous).norm).inter
    (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp E.continuous)))

theorem isOpen_signed_spatial_annular_cone {n : ℕ}
    (i : Fin (n + 1)) (positive : Bool) (ε : ℝ) :
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    IsOpen {y : Domain (n + 1 + 1) |
      (((if positive then (E y).1 i else -(E y).1 i) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), k ≠ i → |(E y).1 k| < (if positive then (E y).1 i else -(E y).1 i)) ∧
        ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε} := by
  intro E
  exact (((isOpen_cubical_signed_cone i positive).preimage (continuous_fst.comp E.continuous)).inter
    (isOpen_Ioo.preimage (continuous_fst.comp E.continuous).norm)).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp E.continuous)))

theorem pairwise_disjoint_spatial_annular_signed_cones (n : ℕ) (ε : ℝ) :
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let C := fun j : Fin (n + 1) × Bool => {y : Domain (n + 1 + 1) |
      (((if j.2 then (E y).1 j.1 else -(E y).1 j.1) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), k ≠ j.1 → |(E y).1 k| < (if j.2 then (E y).1 j.1 else -(E y).1 j.1)) ∧
        ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε}
    Pairwise fun j k => Disjoint (C j) (C k) := by
  intro E C j k hjk
  apply disjoint_left.mpr
  intro y hyj hyk
  exact disjoint_left.mp (pairwise_disjoint_cubical_signed_cones n hjk) hyj.1.1 hyk.1.1

theorem ae_spatial_annular_mem_signed_cone {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) :
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Ω := {y : Domain (n + 1 + 1) | ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1 ∧
      (E y).2 0 ∈ Ioo (0 : ℝ) ε}
    let C := fun j : Fin (n + 1) × Bool => {y : Domain (n + 1 + 1) |
      (((if j.2 then (E y).1 j.1 else -(E y).1 j.1) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), k ≠ j.1 → |(E y).1 k| < (if j.2 then (E y).1 j.1 else -(E y).1 j.1)) ∧
        ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε}
    ∀ᵐ y ∂volume.restrict Ω, ∃ j, y ∈ C j := by
  intro E Ω C
  have hPairs : ∀ᵐ y : Domain (n + 1 + 1) ∂volume,
      ∀ i j : Fin (n + 1), i ≠ j → |(E y).1 i| ≠ |(E y).1 j| := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hne => False.elim (hne hij)
    · have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_inj.mp h)
      exact (ae_ne_abs_coordinates i.castSucc j.castSucc hne).mono fun _ h _ => h
  filter_upwards [ae_restrict_of_ae hPairs,
    ae_restrict_mem (isOpen_spatial_annular_slab n ε).measurableSet] with y hy hyΩ
  have hNot : ¬ ∃ i j k : Fin (n + 1), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      |(E y).1 j| = |(E y).1 i| ∧ |(E y).1 k| = |(E y).1 i| := by
    rintro ⟨i,j,k,hij,_hik,_hjk,hji,_hki⟩
    exact hy j i (Ne.symm hij) hji
  obtain ⟨i,hiPos,hiCase⟩ := cubical_maximum_coordinate_dichotomy (by omega) (E y).1 hNot
  have hStrict : ∀ j : Fin (n + 1), j ≠ i → |(E y).1 j| < |(E y).1 i| := by
    rcases hiCase with h | ⟨j,hij,hEq,_⟩
    · exact h
    · exact False.elim (hy j i (Ne.symm hij) hEq)
  have hTop : |(E y).1 i| < 1 := by
    have h := PiLp.norm_apply_le (E y).1 i
    rw [Real.norm_eq_abs] at h
    exact h.trans_lt hyΩ.1.2
  by_cases hSign : 0 ≤ (E y).1 i
  · refine ⟨(i,true),?_,hyΩ.2⟩
    exact ⟨by simpa only [ite_true,mem_Ioo,abs_of_nonneg hSign] using And.intro (And.intro hiPos hTop) hStrict,hyΩ.1⟩
  · refine ⟨(i,false),?_,hyΩ.2⟩
    exact ⟨by simpa only [Bool.false_eq_true,ite_false,mem_Ioo,abs_of_neg (lt_of_not_ge hSign)] using
      And.intro (And.intro hiPos hTop) hStrict,hyΩ.1⟩

end StratificationTheory
