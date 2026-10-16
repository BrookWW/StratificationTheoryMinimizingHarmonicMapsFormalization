module

public import StratificationTheory.Foundation.CubicalSignedPairPermutation
public import StratificationTheory.Foundation.CubicalLateralPatch

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- A simple physical signed seam lies in an actual finite signed-permutation
frame whose last two coordinates are the standard positive lateral seam. -/
theorem exists_cubical_simple_seam_frame {n : ℕ}
    (x : Domain ((n + 1) + 1)) (i j : Fin ((n + 1) + 1)) (hij : i ≠ j)
    (a b : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ht : 0 < a * x i) (ht1 : a * x i < 1) (htie : a * x i = b * x j)
    (hstrict : ∀ k, k ≠ i → k ≠ j → |x k| < a * x i) :
    ∃ (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool),
      let A := cubicalSignedPermutation ((n + 1) + 1) p s
      let y := A.symm x
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
      let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      0 < (e y).2 0 ∧ (e y).2 0 < 1 ∧
      (c (e y).1).2 0 = (e y).2 0 ∧
      ∀ k : Fin n, |(c (e y).1).1 k| < (e y).2 0 := by
  classical
  obtain ⟨positiveI, hI⟩ : ∃ positive : Bool, ∀ z : ℝ, (if positive then z else -z) = a * z := by
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · exact ⟨true, fun z => by simp⟩
    · exact ⟨false, fun z => by simp⟩
  obtain ⟨positiveJ, hJ⟩ : ∃ positive : Bool, ∀ z : ℝ, (if positive then z else -z) = b * z := by
    rcases sq_eq_one_iff.mp hb with rfl | rfl
    · exact ⟨true, fun z => by simp⟩
    · exact ⟨false, fun z => by simp⟩
  obtain ⟨p, s, hpl, hpm, _hsl, _hsm, hNormal⟩ :=
    exists_cubical_signed_pair_permutation i j hij positiveI positiveJ
  let A := cubicalSignedPermutation ((n + 1) + 1) p s
  let y := A.symm x
  have hLast : y (Fin.last (n + 1)) = a * x i := by
    have h := (hNormal y).1
    rw [A.apply_symm_apply, hI] at h
    exact h.symm
  have hPen : y (Fin.last n).castSucc = b * x j := by
    have h := (hNormal y).2
    rw [A.apply_symm_apply, hJ] at h
    exact h.symm
  refine ⟨p, s, hLast.symm ▸ ht, hLast.symm ▸ ht1, ?_, ?_⟩
  · change y (Fin.last n).castSucc = y (Fin.last (n + 1))
    rw [hPen, hLast, htie]
  · intro k
    change |y k.castSucc.castSucc| < y (Fin.last (n + 1))
    have hki : p k.castSucc.castSucc ≠ i := by
      rw [← hpl]
      exact p.injective.ne (Fin.castSucc_ne_last k.castSucc)
    have hkj : p k.castSucc.castSucc ≠ j := by
      rw [← hpm]
      apply p.injective.ne
      intro heq
      exact Fin.castSucc_ne_last k (Fin.castSucc_inj.mp heq)
    have hAbs := cubicalSignedPermutation_abs_apply p s y k.castSucc.castSucc
    rw [A.apply_symm_apply] at hAbs
    rw [← hAbs, hLast]
    exact hstrict _ hki hkj

end StratificationTheory
