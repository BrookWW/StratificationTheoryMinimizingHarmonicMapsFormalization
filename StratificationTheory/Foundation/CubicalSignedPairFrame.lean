module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps

namespace StratificationTheory

/-- Any two distinct signed physical coordinates are the last two axes of
one literal signed permutation frame, with the actual cube norm preserved. -/
theorem exists_cubical_signed_pair_frame {n : ℕ}
    (i j : Fin ((n + 1) + 1)) (hij : i ≠ j) (positiveI positiveJ : Bool) :
    ∃ (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool)
      (A : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1)),
      p (Fin.last (n + 1)) = i ∧ p (Fin.last n).castSucc = j ∧
      s (Fin.last (n + 1)) = positiveI ∧ s (Fin.last n).castSucc = positiveJ ∧
      (∀ x k, A x (p k) = if s k then x k else -x k) ∧
      (∀ x, ‖WithLp.ofLp (A x)‖ = ‖WithLp.ofLp x‖) ∧
      ∀ x,
        (if positiveI then (A x) i else -(A x) i) = x (Fin.last (n + 1)) ∧
        (if positiveJ then (A x) j else -(A x) j) = x (Fin.last n).castSucc := by
  classical
  let l := Fin.last (n + 1)
  let m := (Fin.last n).castSucc
  let p₀ := Equiv.swap l i
  let k := p₀ j
  have hml : m ≠ l := Fin.castSucc_ne_last (Fin.last n)
  have hkl : k ≠ l := by
    intro hk
    have hj : j = i := by
      have h := congrArg p₀ hk
      simpa only [k, p₀, Equiv.swap_apply_self, Equiv.swap_apply_left] using h
    exact hij hj.symm
  let p := (Equiv.swap m k).trans p₀
  have hpl : p l = i := by
    simp only [p, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hml) (Ne.symm hkl),
      p₀, Equiv.swap_apply_left]
  have hpm : p m = j := by
    simp only [p, Equiv.trans_apply, Equiv.swap_apply_left, k, p₀, Equiv.swap_apply_self]
  let s : Fin ((n + 1) + 1) → Bool := fun a => if a = l then positiveI else if a = m then positiveJ else true
  have hsl : s l = positiveI := by simp only [s, ite_true]
  have hsm : s m = positiveJ := by simp only [s, hml, ite_false, ite_true]
  let A : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1) :=
    (LinearIsometryEquiv.piLpCongrRight 2 (fun a : Fin ((n + 1) + 1) =>
      if s a then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)).trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
  have hApply (x : Domain ((n + 1) + 1)) (a : Fin ((n + 1) + 1)) :
      A x (p a) = if s a then x a else -x a := by
    simp [A, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
    split_ifs <;> rfl
  have hAbs (x : Domain ((n + 1) + 1)) (a : Fin ((n + 1) + 1)) : |A x (p a)| = |x a| := by
    rw [hApply]
    split_ifs <;> simp only [abs_neg]
  have hMax (x : Domain ((n + 1) + 1)) : ‖WithLp.ofLp (A x)‖ = ‖WithLp.ofLp x‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp x))).mpr
      intro a
      have h := hAbs x (p.symm a)
      rw [p.apply_symm_apply] at h
      rw [Real.norm_eq_abs, h]
      exact norm_le_pi_norm (WithLp.ofLp x) _
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp (A x)))).mpr
      intro a
      have h := norm_le_pi_norm (WithLp.ofLp (A x)) (p a)
      simpa only [Real.norm_eq_abs, hAbs] using h
  refine ⟨p, s, A, hpl, hpm, hsl, hsm, hApply, hMax, ?_⟩
  intro x
  have hi := hApply x l
  have hj := hApply x m
  rw [hpl, hsl] at hi
  rw [hpm, hsm] at hj
  constructor
  · rw [hi]
    cases positiveI <;> simp only [l, Bool.false_eq_true, ite_false, ite_true, neg_neg]
  · rw [hj]
    cases positiveJ <;> simp only [m, Bool.false_eq_true, ite_false, ite_true, neg_neg]

end StratificationTheory
