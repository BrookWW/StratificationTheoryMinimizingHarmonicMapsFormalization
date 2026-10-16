module

public import StratificationTheory.Foundation.NormalizedEnergyOrder
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Archimedean.Basic

public section

open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace StratificationTheory.Compactness

private theorem sum_dirichletEnergy_disjoint_le {n q m : ℕ}
    (D : Domain n → Gradient n q) (A : Fin m → Set (Domain n))
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    {U : Set (Domain n)} (hsub : ∀ i, A i ⊆ U) :
    ∑ i, dirichletEnergy D (A i) ≤ dirichletEnergy D U := by
  have hunion : (⋃ i, A i) ⊆ U := iUnion_subset hsub
  have hsum := lintegral_iUnion (μ := volume) hA hdisj
    (fun x => ENNReal.ofReal (hsNormSq (D x)))
  rw [tsum_fintype] at hsum
  change (∑ i, ∫⁻ x in A i, ENNReal.ofReal (hsNormSq (D x))) ≤ _
  rw [← hsum]
  exact lintegral_mono_set hunion

private theorem exists_small_joint_energy_index {n q m : ℕ}
    (D Dv : Domain n → Gradient n q) (A : Fin m → Set (Domain n))
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    {U : Set (Domain n)} (hsub : ∀ i, A i ⊆ U)
    (C η : ℝ≥0) (hC : (C : ℝ) < m * (η : ℝ))
    (hEnergy : dirichletEnergy D U + dirichletEnergy Dv U ≤ C) :
    ∃ i, dirichletEnergy D (A i) + dirichletEnergy Dv (A i) < η := by
  have hsum : (∑ i, (dirichletEnergy D (A i) + dirichletEnergy Dv (A i))) ≤ C := by
    rw [Finset.sum_add_distrib]
    exact (add_le_add (sum_dirichletEnergy_disjoint_le D A hA hdisj hsub)
      (sum_dirichletEnergy_disjoint_le Dv A hA hdisj hsub)).trans hEnergy
  have hconst : (C : ℝ≥0∞) < ∑ _i : Fin m, (η : ℝ≥0∞) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact_mod_cast hC
  obtain ⟨i, _hi, hsmall⟩ := Finset.exists_lt_of_sum_lt (hsum.trans_lt hconst)
  exact ⟨i, hsmall⟩

/-- A common thin concentric shell has arbitrarily small joint energy on
one strictly increasing subsequence of the original gradients. -/
theorem exists_small_energy_shell_subsequence {n q : ℕ}
    (D : ℕ → Domain n → Gradient n q) (Dv : Domain n → Gradient n q)
    (c : Domain n) {s t δ : ℝ} (hs : 0 < s) (hst : s < t) (hδ : 0 < δ)
    (C η : ℝ≥0) (hη : 0 < η)
    (hEnergy : ∀ k, dirichletEnergy (D k) (ball c t) +
      dirichletEnergy Dv (ball c t) ≤ C) :
    ∃ (r R : ℝ) (κ : ℕ → ℕ),
      s ≤ r ∧ r < R ∧ R ≤ t ∧ R ≤ (1 + δ) * r ∧ StrictMono κ ∧
      ∀ k, dirichletEnergy (D (κ k)) {x | r < ‖x - c‖ ∧ ‖x - c‖ < R} +
        dirichletEnergy Dv {x | r < ‖x - c‖ ∧ ‖x - c‖ < R} < η := by
  classical
  have hηR : (0 : ℝ) < η := hη
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((C : ℝ) / η) ((t - s) / (δ * s)))
  have hmC : (C : ℝ) / η < m := (le_max_left _ _).trans_lt hm
  have hmδ : (t - s) / (δ * s) < m := (le_max_right _ _).trans_lt hm
  have hmpos : (0 : ℝ) < m := (div_nonneg C.coe_nonneg hηR.le).trans_lt hmC
  have hC : (C : ℝ) < m * (η : ℝ) := (div_lt_iff₀ hηR).mp hmC
  have hwidth : (t - s) / m < δ * s := by
    apply (div_lt_iff₀ hmpos).mpr
    have h := (div_lt_iff₀ (mul_pos hδ hs)).mp hmδ
    simpa only [mul_comm] using h
  let d : ℝ := (t - s) / m
  have hd : 0 < d := div_pos (sub_pos.mpr hst) hmpos
  let a : ℕ → ℝ := fun j => s + j * d
  let A : Fin m → Set (Domain n) := fun i =>
    {x | a i.val < ‖x - c‖ ∧ ‖x - c‖ < a (i.val + 1)}
  have hA (i : Fin m) : MeasurableSet (A i) :=
    (isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm).measurableSet
  have ha (i : Fin m) : s ≤ a i.val := by
    dsimp only [a]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd.le)
  have hab (i : Fin m) : a i.val < a (i.val + 1) := by
    dsimp only [a]
    push_cast
    linarith only [hd]
  have ht (i : Fin m) : a (i.val + 1) ≤ t := by
    have him : (i.val + 1 : ℝ) ≤ m := by exact_mod_cast i.isLt
    have hle := mul_le_mul_of_nonneg_right him hd.le
    have hmd : (m : ℝ) * d = t - s := mul_div_cancel₀ _ hmpos.ne'
    dsimp only [a]
    push_cast
    linarith only [hle, hmd]
  have hdisj : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · have hle : a (i.val + 1) ≤ a j.val := by
        dsimp only [a]
        have hij' : (i.val + 1 : ℝ) ≤ j.val := by exact_mod_cast hlt
        simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hij' hd.le) s
      exact (hxi.2.trans_le hle).not_ge hxj.1.le
    · have hle : a (j.val + 1) ≤ a i.val := by
        dsimp only [a]
        have hji' : (j.val + 1 : ℝ) ≤ i.val := by exact_mod_cast hgt
        simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hji' hd.le) s
      exact (hxj.2.trans_le hle).not_ge hxi.1.le
  have hsub (i : Fin m) : A i ⊆ ball c t := fun _ hx =>
    mem_ball_iff_norm.mpr (hx.2.trans_le (ht i))
  have hchoice (k : ℕ) : ∃ i : Fin m,
      dirichletEnergy (D k) (A i) + dirichletEnergy Dv (A i) < η :=
    exists_small_joint_energy_index (D k) Dv A hA hdisj hsub C η hC (hEnergy k)
  choose j hj using hchoice
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber j
  have hi' : {k | j k = i}.Infinite := by
    exact Set.infinite_coe_iff.mp hi
  let κ := Nat.nth (fun k => j k = i)
  have hκ : StrictMono κ := Nat.nth_strictMono hi'
  refine ⟨a i.val, a (i.val + 1), κ, ha i, hab i, ht i, ?_, hκ, ?_⟩
  · have hstep : a (i.val + 1) = a i.val + d := by
      dsimp only [a]
      push_cast
      ring
    have hδs := mul_le_mul_of_nonneg_left (ha i) hδ.le
    rw [hstep]
    linarith only [hwidth, hδs]
  · intro k
    have hki : j (κ k) = i := Nat.nth_mem_of_infinite hi' k
    simpa only [hki] using hj (κ k)

end StratificationTheory.Compactness
