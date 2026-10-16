module

public import StratificationTheory.Foundation.CubicalBoundaryFromFaces
public import StratificationTheory.Foundation.CubicalSignedPermutations

public section

open HarmonicMaps

namespace StratificationTheory

/-- A genuine permutation fixing the last coordinate restricts to a genuine
permutation of all remaining coordinates. -/
theorem exists_fin_permutation_restriction {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (hp : p (Fin.last n) = Fin.last n) :
    ∃ r : Equiv.Perm (Fin n), ∀ k : Fin n, (r k).castSucc = p k.castSucc := by
  have hnot (k : Fin n) : p k.castSucc ≠ Fin.last n := by
    rw [← hp]
    exact p.injective.ne (Fin.castSucc_ne_last k)
  let f : Fin n → Fin n := fun k => Fin.castLT (p k.castSucc) (Fin.val_lt_last (hnot k))
  have hf (k : Fin n) : (f k).castSucc = p k.castSucc := Fin.ext rfl
  have hinj : Function.Injective f := by
    intro k l h
    apply Fin.castSucc_inj.mp
    apply p.injective
    rw [← hf k, ← hf l, h]
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- Every literal finite ambient frame restricts to one literal finite
tangential signed permutation on its original canonical signed face. -/
theorem exists_cubical_signed_frame_face_restriction {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let A := cubicalSignedPermutation (n + 1) p s
    let Q := cubicalSignedFaceIsometry n (p (Fin.last n)) (s (Fin.last n))
    ∃ (r : Equiv.Perm (Fin n)) (t : Fin n → Bool),
      (∀ k : Fin n, t k = s k.castSucc) ∧
      ∀ x : Domain n, A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) =
        Q (e.symm (cubicalSignedPermutation n r t x, EuclideanSpace.single (0 : Fin 1) 1)) := by
  intro e A Q
  let σ := Equiv.swap (Fin.last n) (p (Fin.last n))
  let p₀ := p.trans σ
  have hp₀ : p₀ (Fin.last n) = Fin.last n := Equiv.swap_apply_right _ _
  obtain ⟨r, hr⟩ := exists_fin_permutation_restriction p₀ hp₀
  let t : Fin n → Bool := fun k => s k.castSucc
  have hcapLast (x : Domain n) : (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) (Fin.last n) = 1 := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).2 0 = 1
    rw [e.apply_symm_apply]
    rfl
  have hcapBase (x : Domain n) (k : Fin n) :
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) k.castSucc = x k := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).1 k = x k
    rw [e.apply_symm_apply]
  refine ⟨r, t, fun _ => rfl, ?_⟩
  intro x
  ext l
  obtain ⟨k, rfl⟩ := p.surjective l
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [cubicalSignedPermutation_apply, hcapLast]
    have hQ := cubicalSignedFaceIsometry_apply (p (Fin.last n)) (s (Fin.last n))
      (e.symm (cubicalSignedPermutation n r t x, EuclideanSpace.single (0 : Fin 1) 1)) (Fin.last n)
    simpa only [Equiv.swap_apply_left, ite_true, hcapLast] using hQ.symm
  · rw [cubicalSignedPermutation_apply, hcapBase]
    have hcoord : σ (r k).castSucc = p k.castSucc := by
      rw [hr]
      exact Equiv.swap_apply_self _ _ _
    have hQ := cubicalSignedFaceIsometry_apply (p (Fin.last n)) (s (Fin.last n))
      (e.symm (cubicalSignedPermutation n r t x, EuclideanSpace.single (0 : Fin 1) 1)) (r k).castSucc
    rw [if_neg (Fin.castSucc_ne_last (r k)), hcapBase, cubicalSignedPermutation_apply] at hQ
    rw [← hcoord]
    exact hQ.symm

end StratificationTheory
