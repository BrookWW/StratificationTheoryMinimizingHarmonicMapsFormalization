module

public import StratificationTheory.Foundation.CubicalConePartition
public import StratificationTheory.Foundation.CubicalConeGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section

open HarmonicMaps MeasureTheory Set Filter

namespace StratificationTheory

/-- Every literal signed strict face cone is an open Euclidean domain. -/
theorem isOpen_cubical_signed_cone {n : ℕ} (i : Fin (n + 1)) (positive : Bool) :
    IsOpen {x : Domain (n + 1) |
      (if positive then x i else -x i) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ j : Fin (n + 1), j ≠ i → |x j| < (if positive then x i else -x i)} := by
  classical
  have hC : Continuous (fun x : Domain (n + 1) => if positive then x i else -x i) := by
    cases positive
    · exact (EuclideanSpace.proj i).continuous.neg
    · exact (EuclideanSpace.proj i).continuous
  apply IsOpen.inter
  · exact isOpen_Ioo.preimage hC
  · change IsOpen {x : Domain (n + 1) | ∀ j : Fin (n + 1), j ≠ i →
      |x j| < (if positive then x i else -x i)}
    have hset : {x : Domain (n + 1) | ∀ j : Fin (n + 1), j ≠ i →
        |x j| < (if positive then x i else -x i)} =
        ⋂ j : {j : Fin (n + 1) // j ≠ i},
          {x | |x j.val| < (if positive then x i else -x i)} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter, Subtype.forall]
    rw [hset]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (EuclideanSpace.proj j.val).continuous.abs hC

/-- Different actual Euclidean coordinates have distinct absolute values
outside a null union of two genuine coordinate hyperplanes. -/
theorem ae_ne_abs_coordinates {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    ∀ᵐ x : Domain d ∂volume, |x i| ≠ |x j| := by
  let Lminus : Domain d →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj i).toLinearMap - (EuclideanSpace.proj j).toLinearMap
  let Lplus : Domain d →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj i).toLinearMap + (EuclideanSpace.proj j).toLinearMap
  have hminus : LinearMap.ker Lminus ≠ ⊤ := by
    intro htop
    have hm : EuclideanSpace.single i (1 : ℝ) ∈ LinearMap.ker Lminus := by rw [htop]; trivial
    change (EuclideanSpace.single i (1 : ℝ)) i - (EuclideanSpace.single i (1 : ℝ)) j = 0 at hm
    simp [(Ne.symm hij)] at hm
  have hplus : LinearMap.ker Lplus ≠ ⊤ := by
    intro htop
    have hm : EuclideanSpace.single i (1 : ℝ) ∈ LinearMap.ker Lplus := by rw [htop]; trivial
    change (EuclideanSpace.single i (1 : ℝ)) i + (EuclideanSpace.single i (1 : ℝ)) j = 0 at hm
    simp [(Ne.symm hij)] at hm
  have hm := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_submodule volume _ hminus)
  have hp := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_submodule volume _ hplus)
  filter_upwards [hm, hp] with x hxminus hxplus hEq
  rcases abs_eq_abs.mp hEq with heq | heq
  · apply hxminus
    change x i - x j = 0
    exact sub_eq_zero.mpr heq
  · apply hxplus
    change x i + x j = 0
    rw [heq, neg_add_cancel]

/-- The open signed dominant-coordinate cones are pointwise disjoint. -/
theorem pairwise_disjoint_cubical_signed_cones (n : ℕ) :
    let C : (Fin (n + 1) × Bool) → Set (Domain (n + 1)) := fun p =>
      {x | (if p.2 then x p.1 else -x p.1) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ j : Fin (n + 1), j ≠ p.1 → |x j| < (if p.2 then x p.1 else -x p.1)}
    Pairwise fun p q => Disjoint (C p) (C q) := by
  intro C p q hpq
  apply disjoint_left.mpr
  intro x hxp hxq
  rcases p with ⟨i, s⟩
  rcases q with ⟨j, t⟩
  by_cases hij : i = j
  · subst j
    cases s <;> cases t
    · exact hpq rfl
    · have h₁ := hxp.1.1
      have h₂ := hxq.1.1
      change 0 < -x i at h₁
      change 0 < x i at h₂
      linarith only [h₁, h₂]
    · have h₁ := hxp.1.1
      have h₂ := hxq.1.1
      change 0 < x i at h₁
      change 0 < -x i at h₂
      linarith only [h₁, h₂]
    · exact hpq rfl
  · have hAbsI : |x i| = (if s then x i else -x i) := by
      cases s
      · simpa only [Bool.false_eq_true, ite_false, abs_neg] using abs_of_pos hxp.1.1
      · exact abs_of_pos hxp.1.1
    have hAbsJ : |x j| = (if t then x j else -x j) := by
      cases t
      · simpa only [Bool.false_eq_true, ite_false, abs_neg] using abs_of_pos hxq.1.1
      · exact abs_of_pos hxq.1.1
    have hji := hxp.2 j (Ne.symm hij)
    have hij' := hxq.2 i hij
    rw [hAbsJ] at hji
    rw [hAbsI] at hij'
    exact (hji.trans hij').false

/-- Every strict signed face cone lies in the literal open unit cube. -/
theorem cubical_signed_cone_subset_unit_cube {n : ℕ} (i : Fin (n + 1)) (positive : Bool) :
    {x : Domain (n + 1) | (if positive then x i else -x i) ∈ Ioo (0 : ℝ) 1 ∧
      ∀ j : Fin (n + 1), j ≠ i → |x j| < (if positive then x i else -x i)} ⊆
        ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1 := by
  intro x hx
  apply (mem_unit_coordinate_face_iff x).mpr
  intro j
  by_cases hji : j = i
  · subst j
    have hAbs : |x i| = (if positive then x i else -x i) := by
      cases positive
      · simpa only [Bool.false_eq_true, ite_false, abs_neg] using abs_of_pos hx.1.1
      · exact abs_of_pos hx.1.1
    rw [hAbs]
    exact hx.1.2
  · exact (hx.2 j hji).trans hx.1.2

/-- The same finite signed face cones cover the actual open cube up to
ambient volume zero. -/
theorem ae_unit_cube_mem_cubical_signed_cone {n : ℕ} (hn : 2 ≤ n) :
    let B := ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let C : (Fin (n + 1) × Bool) → Set (Domain (n + 1)) := fun p =>
      {x | (if p.2 then x p.1 else -x p.1) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ j : Fin (n + 1), j ≠ p.1 → |x j| < (if p.2 then x p.1 else -x p.1)}
    ∀ᵐ x ∂volume.restrict B, ∃ p : Fin (n + 1) × Bool, x ∈ C p := by
  intro B C
  have hPairs : ∀ᵐ x : Domain (n + 1) ∂volume, ∀ i j : Fin (n + 1), i ≠ j → |x i| ≠ |x j| := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hne => False.elim (hne hij)
    · exact (ae_ne_abs_coordinates i j hij).mono fun _ h _ => h
  have hB : MeasurableSet B := MeasurableSet.iInter fun j =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj j).continuous.measurable
  filter_upwards [ae_restrict_of_ae hPairs, ae_restrict_mem hB] with x hx hxB
  have hnot : ¬ ∃ i j k : Fin (n + 1), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      |x j| = |x i| ∧ |x k| = |x i| := by
    rintro ⟨i, j, k, hij, _hik, _hjk, hji, _hki⟩
    exact hx j i (Ne.symm hij) hji
  obtain ⟨i, hiPos, hiCase⟩ := cubical_maximum_coordinate_dichotomy (by omega) x hnot
  have hstrict : ∀ j : Fin (n + 1), j ≠ i → |x j| < |x i| := by
    rcases hiCase with h | ⟨j, hij, hjEq, _hother⟩
    · exact h
    · exact False.elim (hx j i (Ne.symm hij) hjEq)
  have hcube := mem_unit_coordinate_face_iff x |>.mp hxB
  by_cases hsign : 0 ≤ x i
  · refine ⟨(i, true), ?_⟩
    change (x i ∈ Ioo (0 : ℝ) 1) ∧ ∀ j : Fin (n + 1), j ≠ i → |x j| < x i
    simpa only [mem_Ioo, abs_of_nonneg hsign] using And.intro (And.intro hiPos (hcube i)) hstrict
  · refine ⟨(i, false), ?_⟩
    change (-x i ∈ Ioo (0 : ℝ) 1) ∧ ∀ j : Fin (n + 1), j ≠ i → |x j| < -x i
    simpa only [mem_Ioo, abs_of_neg (lt_of_not_ge hsign)] using And.intro (And.intro hiPos (hcube i)) hstrict

end StratificationTheory
