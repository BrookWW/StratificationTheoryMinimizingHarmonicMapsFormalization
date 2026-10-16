module

public import StratificationTheory.Foundation.UniformGridCarriers

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- A genuine shared mesh face meeting the first open temporal slab is
spatial, and both neighboring cells have the original temporal index zero. -/
theorem uniformGrid_shared_face_in_first_time_slab {n N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : Domain (n + 1)) (htime : x (Fin.last n) ∈ Ioo (0 : ℝ) ε)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (hzi : 0 < (z i).val)
    (hxi : x i = ((z i).val : ℝ) * ε)
    (hother : ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) :
    i ≠ Fin.last n ∧ (z (Fin.last n)).val = 0 := by
  have hnot : i ≠ Fin.last n := by
    intro hi
    have hcast : (1 : ℝ) ≤ (z i).val := by exact_mod_cast hzi
    have hle := mul_le_mul_of_nonneg_right hcast hε.le
    rw [← hxi, hi] at hle
    linarith [htime.2]
  refine ⟨hnot, ?_⟩
  by_contra hnonzero
  have hpos : 0 < (z (Fin.last n)).val := Nat.pos_of_ne_zero hnonzero
  have hcast : (1 : ℝ) ≤ (z (Fin.last n)).val := by exact_mod_cast hpos
  have hle := mul_le_mul_of_nonneg_right hcast hε.le
  have hx := hother (Fin.last n) hnot.symm
  linarith [hx.1, htime.2]

/-- Every cell with positive temporal index misses the entire first open
time slab, so it contributes no physical map, energy, or trace obligation
on that slab. -/
theorem uniformGrid_positive_time_cell_misses_first_slab {n N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (z : Fin (n + 1) → Fin N) (hz : 0 < (z (Fin.last n)).val) :
    (uniformGridCell (n + 1) N ε z).val ∩ {x : Domain (n + 1) | x (Fin.last n) ∈ Ioo (0 : ℝ) ε} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcell := (mem_uniformGridCell_iff _ _ _ z x).mp hx.1 (Fin.last n)
  have hcast : (1 : ℝ) ≤ (z (Fin.last n)).val := by exact_mod_cast hz
  have hle := mul_le_mul_of_nonneg_right hcast hε.le
  linarith [hcell.1, hx.2.2]

/-- The actual zero-temporal-index mesh cell is precisely its original
spatial open cell times the single original physical time interval. -/
theorem uniformGrid_first_time_cell_product {n N : ℕ} (hN : 0 < N) (ε : ℝ)
    (z : Fin n → Fin N) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j : Fin N := ⟨0, hN⟩
    (uniformGridCell (n + 1) N ε (Fin.snoc z j)).val =
      {x | (e x).1 ∈ (uniformGridCell n N ε z).val ∧ (e x).2 0 ∈ Ioo (0 : ℝ) ε} := by
  intro e j
  ext x
  rw [mem_uniformGridCell_iff]
  constructor
  · intro h
    refine ⟨(mem_uniformGridCell_iff _ _ _ z _).mpr ?_, ?_⟩
    · intro k
      change x k.castSucc ∈ _
      simpa only [Fin.snoc_castSucc] using h k.castSucc
    · change x (Fin.last n) ∈ Ioo (0 : ℝ) ε
      simpa only [Fin.snoc_last, j, Nat.cast_zero, zero_mul, zero_add, one_mul] using h (Fin.last n)
  · rintro ⟨hBase, hTime⟩ k
    change x (Fin.last n) ∈ Ioo (0 : ℝ) ε at hTime
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simpa only [Fin.snoc_last, j, Nat.cast_zero, zero_mul, zero_add, one_mul] using hTime
    · have hk := (mem_uniformGridCell_iff _ _ _ z _).mp hBase k
      change x k.castSucc ∈ Ioo ((z k).val * ε) (((z k).val + (1 : ℝ)) * ε) at hk
      simpa only [Fin.snoc_castSucc] using hk

end StratificationTheory
