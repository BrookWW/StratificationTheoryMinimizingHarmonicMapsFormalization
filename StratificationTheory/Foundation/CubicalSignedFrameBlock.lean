module

public import StratificationTheory.Foundation.CubicalFrameFaceRestriction

public section

open HarmonicMaps

namespace StratificationTheory

/-- The actual finite tangential frame restriction holds on every native
height, with the same tangential signed permutation. -/
theorem exists_cubical_signed_frame_block {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let A := cubicalSignedPermutation (n + 1) p s
    let Q := cubicalSignedFaceIsometry n (p (Fin.last n)) (s (Fin.last n))
    ∃ (r : Equiv.Perm (Fin n)) (t : Fin n → Bool),
      (∀ k : Fin n, t k = s k.castSucc) ∧
      ∀ (x : Domain n) (η : ℝ), A (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
        Q (e.symm (cubicalSignedPermutation n r t x, EuclideanSpace.single (0 : Fin 1) η)) := by
  intro e A Q
  obtain ⟨r, t, ht, hFace⟩ := exists_cubical_signed_frame_face_restriction p s
  let B := cubicalSignedPermutation n r t
  have hNative (x : Domain n) (η : ℝ) : e.symm (x, EuclideanSpace.single (0 : Fin 1) η) =
      e.symm (x, EuclideanSpace.single (0 : Fin 1) 1) +
        (η - 1) • e.symm (0, EuclideanSpace.single (0 : Fin 1) 1) := by
    apply e.injective
    simp only [map_add, map_smul, e.apply_symm_apply]
    apply Prod.ext
    · simp
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp only [Prod.snd_add, Prod.smul_snd, PiLp.add_apply, PiLp.smul_apply,
        PiLp.single_apply, ite_true, smul_eq_mul]
      ring
  refine ⟨r, t, ht, ?_⟩
  intro x η
  rw [hNative x η, A.map_add, A.map_smul, hFace, hFace]
  change Q (e.symm (B x, _)) + (η - 1) • Q (e.symm (B 0, _)) = _
  rw [B.map_zero, ← Q.map_smul, ← Q.map_add, ← hNative]

/-- An oriented canonical face chart is the positive chart with the exact
physical normal height reflected when the outward sign is negative. -/
theorem cubical_signed_face_native_height {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (x : Domain n) (η : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    cubicalSignedFaceIsometry n i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
      cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then η else -η))) := by
  intro e
  ext l
  obtain ⟨k, rfl⟩ := (Equiv.swap (Fin.last n) i).surjective l
  rw [cubicalSignedFaceIsometry_apply, cubicalSignedFaceIsometry_apply]
  by_cases hk : k = Fin.last n
  · subst k
    simp only [ite_true]
    have hnormal (r : ℝ) : (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)) (Fin.last n) = r := by
      change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))).2 0 = r
      rw [e.apply_symm_apply]
      rfl
    rw [hnormal, hnormal]
  · rw [if_neg hk, if_neg hk]
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hk
    rw [← hj]
    change (e (e.symm (x, _))).1 j = (e (e.symm (x, _))).1 j
    rw [e.apply_symm_apply, e.apply_symm_apply]

end StratificationTheory
