module

public import StratificationTheory.Foundation.CubicalSignedPermutations

public section

open HarmonicMaps

namespace StratificationTheory

/-- Every actual spatial coordinate permutation lifts to a genuine finite
signed frame of the prism. The last time coordinate is fixed on the entire
carrier, with exact forward and inverse native block formulas. -/
theorem exists_prism_spatial_permutation {d : ℕ} (r : Equiv.Perm (Fin d)) :
    ∃ p : Equiv.Perm (Fin (d + 1)),
      let R := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ r
      let A := cubicalSignedPermutation (d + 1) p (fun _ => true)
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
      (∀ j : Fin d, p j.castSucc = (r j).castSucc) ∧ p (Fin.last d) = Fin.last d ∧
      (∀ z, A z = e.symm (R (e z).1, (e z).2)) ∧
      (∀ z, A.symm z = e.symm (R.symm (e z).1, (e z).2)) ∧
      ∀ z, (e (A z)).2 = (e z).2 := by
  let p : Equiv.Perm (Fin (d + 1)) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr r (Equiv.refl (Fin 1)))).trans finSumFinEquiv
  have hp (j : Fin d) : p j.castSucc = (r j).castSucc := by
    simp [p]
    rfl
  have hpLast : p (Fin.last d) = Fin.last d := by
    simp [p, finSumFinEquiv_symm_last]
    rfl
  refine ⟨p, ?_⟩
  intro R A e
  have hA (z : Domain (d + 1)) (j : Fin (d + 1)) : A z (p j) = z j := by
    exact (cubicalSignedPermutation_apply p (fun _ => true) z j).trans (if_pos rfl)
  have hFormula (z : Domain (d + 1)) : A z = e.symm (R (e z).1, (e z).2) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · ext j
      obtain ⟨b, rfl⟩ := r.surjective j
      have h := hA z b.castSucc
      rw [hp] at h
      change A z (r b).castSucc = R (e z).1 (r b)
      rw [h]
      have hR : R (e z).1 (r b) = (e z).1 b := by
        simp [R, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
      rw [hR]
      rfl
    · ext j
      have h := hA z (Fin.last d)
      rw [hpLast] at h
      have hTime (v : Domain (d + 1)) : (e v).2 0 = v (Fin.last d) := rfl
      rw [Subsingleton.elim j (0 : Fin 1), hTime, hTime]
      exact h
  refine ⟨hp, hpLast, hFormula, ?_, ?_⟩
  · intro z
    apply A.injective
    rw [A.apply_symm_apply, hFormula, e.apply_symm_apply, R.apply_symm_apply, e.symm_apply_apply]
  · intro z
    rw [hFormula, e.apply_symm_apply]

end StratificationTheory
