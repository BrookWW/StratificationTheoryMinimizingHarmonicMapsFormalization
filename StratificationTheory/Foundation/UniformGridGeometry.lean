module

public import StratificationTheory.Foundation.UniformGridScalar
public import StratificationTheory.Foundation.CoordinateBoxFaceChart
public import StratificationTheory.Foundation.CoordinatePiecewiseSobolevData

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators

namespace StratificationTheory

/-- Every actual coordinate hyperplane is native-volume null. -/
theorem ae_physical_coordinate_ne {n : ℕ} (i : Fin (n + 1)) (a : ℝ) :
    ∀ᵐ x : Domain (n + 1) ∂volume, x i ≠ a := by
  let Q := cubicalSignedFaceIsometry n i true
  have h := Q.symm.measurePreserving.quasiMeasurePreserving.ae (ae_native_time_ne n a)
  have hTime (x : Domain (n + 1)) :
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)) (Q.symm x)).2 0 = x i := by
    change Q.symm x (Fin.last n) = x i
    simpa only [ite_true] using cubicalSignedFaceIsometry_symm_apply i true x (Fin.last n)
  simpa only [hTime] using h

/-- The original uniform open mesh cells are pairwise disjoint. -/
theorem pairwise_disjoint_uniform_grid_cells (d N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let C := fun z : Fin d → Fin N => {x : Domain d | ∀ i : Fin d,
      x i ∈ Ioo ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε)}
    Pairwise fun z w => Disjoint (C z) (C w) := by
  intro C z w hzw
  apply disjoint_left.mpr
  intro x hxz hxw
  have hne : ∃ i : Fin d, z i ≠ w i := by
    by_contra! h
    exact hzw (funext h)
  obtain ⟨i, hi⟩ := hne
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hcast : ((z i).val : ℝ) + 1 ≤ (w i).val := by exact_mod_cast Nat.succ_le_iff.mpr hlt
    have hle := mul_le_mul_of_nonneg_right hcast hε.le
    linarith [(hxz i).2, (hxw i).1]
  · have hcast : ((w i).val : ℝ) + 1 ≤ (z i).val := by exact_mod_cast Nat.succ_le_iff.mpr hgt
    have hle := mul_le_mul_of_nonneg_right hcast hε.le
    linarith [(hxw i).2, (hxz i).1]

/-- The actual open mesh cells cover the full positive box outside a finite
null family of original coordinate grid hyperplanes. -/
theorem ae_uniform_grid_cell_cover (n N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x : Domain (n + 1) ∂volume.restrict {x | ∀ i : Fin (n + 1), x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)},
      ∃ z : Fin (n + 1) → Fin N, ∀ i : Fin (n + 1),
        x i ∈ Ioo ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε) := by
  have hAll : ∀ᵐ x : Domain (n + 1) ∂volume, ∀ i : Fin (n + 1), ∀ k : Fin N,
      x i ≠ (k.val : ℝ) * ε :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => ae_physical_coordinate_ne i _
  have hMeas : MeasurableSet {x : Domain (n + 1) | ∀ i, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)} :=
    by
      have hEq : {x : Domain (n + 1) | ∀ i, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)} =
          ⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) ((N : ℝ) * ε) := by
        ext x
        simp only [mem_setOf_eq, mem_iInter, mem_preimage]
        rfl
      rw [hEq]
      exact MeasurableSet.iInter fun i => measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable
  filter_upwards [ae_restrict_of_ae hAll, ae_restrict_mem hMeas] with x hx hxΩ
  have hCell (i : Fin (n + 1)) : ∃ k : Fin N,
      x i ∈ Ioo ((k.val : ℝ) * ε) (((k.val : ℝ) + 1) * ε) := by
    rcases uniform_grid_interval_or_cut hε (hxΩ i) with h | ⟨k, _hk, heq⟩
    · exact h
    · exact False.elim (hx i k heq)
  choose z hz using hCell
  exact ⟨z, hz⟩

/-- Off actual intersections of two grid directions, every point lies in
one original open cell or on one genuine shared face between adjacent cells. -/
theorem uniform_grid_cell_or_simple_face {d N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : Domain d) (hx : ∀ i : Fin d, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)) :
    let T : Finset ℝ := Finset.univ.image (fun k : Fin N => (k.val : ℝ) * ε)
    (¬ ∃ i j : Fin d, i ≠ j ∧ x i ∈ T ∧ x j ∈ T) →
    (∃ z : Fin d → Fin N, ∀ i, x i ∈ Ioo ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε)) ∨
      ∃ (i : Fin d) (z : Fin d → Fin N), 0 < (z i).val ∧ x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε) := by
  classical
  intro T hnot
  have hNoncut (i : Fin d) (hi : x i ∉ T) : ∃ k : Fin N,
      x i ∈ Ioo ((k.val : ℝ) * ε) (((k.val : ℝ) + 1) * ε) := by
    rcases uniform_grid_interval_or_cut hε (hx i) with h | ⟨k, _hk, heq⟩
    · exact h
    · exact False.elim (hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, heq.symm⟩))
  by_cases hAll : ∀ i : Fin d, x i ∉ T
  · choose z hz using fun i => hNoncut i (hAll i)
    exact Or.inl ⟨z, hz⟩
  · push Not at hAll
    obtain ⟨i, hi⟩ := hAll
    obtain ⟨k, _hk, hkx⟩ := Finset.mem_image.mp hi
    have hkPos : 0 < k.val := by
      by_contra hk
      have hk0 : k.val = 0 := by omega
      have hxi := (hx i).1
      rw [← hkx, hk0, Nat.cast_zero, zero_mul] at hxi
      exact lt_irrefl _ hxi
    have hOther (j : Fin d) (hji : j ≠ i) : ∃ l : Fin N,
        x j ∈ Ioo ((l.val : ℝ) * ε) (((l.val : ℝ) + 1) * ε) :=
      hNoncut j (fun hj => hnot ⟨i, j, hji.symm, hi, hj⟩)
    let z : Fin d → Fin N := fun j => if h : j = i then k else Classical.choose (hOther j h)
    refine Or.inr ⟨i, z, by simpa only [z, dite_true] using hkPos,
      by simpa only [z, dite_true] using hkx.symm, ?_⟩
    intro j hji
    simpa only [z, dif_neg hji] using Classical.choose_spec (hOther j hji)

/-- Every finite positive coordinate box is genuinely Euclidean bounded. -/
theorem isBounded_positive_coordinate_box (d : ℕ) (L : ℝ) :
    Bornology.IsBounded {x : Domain d | ∀ i : Fin d, x i ∈ Ioo (0 : ℝ) L} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(d : ℝ) * |L|, ?_⟩
  intro x hx
  have hrepr : ∑ i : Fin d, EuclideanSpace.single i (x i) = x := by ext i; simp
  calc
    ‖x‖ = ‖∑ i : Fin d, EuclideanSpace.single i (x i)‖ := congrArg norm hrepr.symm
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, |L| := Finset.sum_le_sum fun i _ => by
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (hx i).1]
      exact (hx i).2.le.trans (le_abs_self L)
    _ = (d : ℝ) * |L| := by simp

end StratificationTheory
