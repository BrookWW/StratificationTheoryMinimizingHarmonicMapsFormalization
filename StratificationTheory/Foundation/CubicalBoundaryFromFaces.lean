module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import StratificationTheory.Foundation.CubicalConeGeometry
import Mathlib.Data.Finset.Max

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- Independent original maps on the signed open faces have one actual
ambient boundary representative. Every carrier value comes from a maximal
coordinate face; on each open face the representative is exactly original. -/
theorem exists_cubical_boundary_from_face_maps {n q : ℕ}
    (f : (Fin (n + 1) × Bool) → Domain n → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    ∃ G : Domain (n + 1) → Ambient q,
      (∀ y : Domain (n + 1), ∃ (i : Fin (n + 1)) (positive : Bool),
        |y i| = ‖WithLp.ofLp y‖ ∧ (if positive then y i else -y i) = |y i| ∧
        G y = f (i, positive) ((e ((cubicalSignedFaceIsometry n i positive).symm y)).1)) ∧
      ∀ (i : Fin (n + 1)) (positive : Bool) (x : Domain n), x ∈ B →
        G (cubicalSignedFaceIsometry n i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = f (i, positive) x := by
  classical
  intro e B
  let M : Domain (n + 1) → Fin (n + 1) := fun y => Classical.choose
    (Finset.exists_max_image Finset.univ (fun i : Fin (n + 1) => |y i|) Finset.univ_nonempty)
  have hMax (y : Domain (n + 1)) (i : Fin (n + 1)) : |y i| ≤ |y (M y)| :=
    (Classical.choose_spec (Finset.exists_max_image Finset.univ
      (fun i : Fin (n + 1) => |y i|) Finset.univ_nonempty)).2 i (Finset.mem_univ i)
  let sign : Domain (n + 1) → Bool := fun y => decide (0 ≤ y (M y))
  let G : Domain (n + 1) → Ambient q := fun y =>
    f (M y, sign y) ((e ((cubicalSignedFaceIsometry n (M y) (sign y)).symm y)).1)
  refine ⟨G, ?_, ?_⟩
  · intro y
    refine ⟨M y, sign y, ?_, ?_, rfl⟩
    · apply le_antisymm
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm (WithLp.ofLp y) (M y)
      · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (y (M y)))).mpr
        intro i
        change |y i| ≤ |y (M y)|
        exact hMax y i
    · by_cases hy : 0 ≤ y (M y)
      · simp [sign, hy, abs_of_nonneg hy]
      · simp [sign, hy, abs_of_neg (lt_of_not_ge hy)]
  · intro i positive x hx
    let Q := cubicalSignedFaceIsometry n i positive
    let y := Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    have hNormal : y i = if positive then 1 else -1 := by
      have h := cubicalSignedFaceIsometry_apply i positive
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) (Fin.last n)
      have hCap : (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) (Fin.last n) = 1 := by
        change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).2 0 = 1
        rw [e.apply_symm_apply]
        rfl
      simpa only [Equiv.swap_apply_left, ite_true, hCap] using h
    have hAbs : |y i| = 1 := by rw [hNormal]; cases positive <;> norm_num
    have hOther (k : Fin (n + 1)) (hki : k ≠ i) : |y k| < 1 := by
      rw [cubicalSignedFaceIsometry_abs_apply]
      let l := (Equiv.swap (Fin.last n) i) k
      have hl : l ≠ Fin.last n := by
        intro heq
        have hinj := (Equiv.swap (Fin.last n) i).injective
        apply hki
        apply hinj
        simpa only [Equiv.swap_apply_right] using heq
      obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hl
      rw [show (Equiv.swap (Fin.last n) i) k = j.castSucc from hj.symm]
      change |(e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).1 j| < 1
      rw [e.apply_symm_apply]
      exact (mem_unit_coordinate_face_iff x).mp hx j
    have hMi : M y = i := by
      by_contra hne
      have hle := hMax y i
      rw [hAbs] at hle
      exact (not_lt_of_ge hle) (hOther (M y) hne)
    have hSign : sign y = positive := by
      dsimp [sign]
      rw [hMi, hNormal]
      cases positive <;> norm_num
    change G y = _
    dsimp [G]
    rw [hMi, hSign]
    change f (i, positive) ((e (Q.symm (Q _))).1) = _
    rw [Q.symm_apply_apply, e.apply_symm_apply]

end StratificationTheory
