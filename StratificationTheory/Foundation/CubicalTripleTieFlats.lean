module

public import StratificationTheory.Foundation.CoordinateTripleTiePlane

public section

open HarmonicMaps Set

namespace StratificationTheory

private theorem exists_bool_sign_mul_of_abs_eq {a b : ℝ} (h : |b| = |a|) :
    ∃ s : Bool, b = (if s then (1 : ℝ) else -1) * a := by
  rcases abs_eq_abs.mp h with h | h
  · exact ⟨true, by simpa only [Bool.true_eq, ite_true, one_mul] using h⟩
  · exact ⟨false, by simpa only [Bool.false_eq_true, ite_false, neg_one_mul] using h⟩

/-- All signed triple-coordinate tie planes form one genuine finite family
of the exact transverse kernels used by codimension-two removability. -/
theorem exists_cubical_triple_tie_flat_isometries (n : ℕ) :
    let I := (Fin 3 ↪ Fin (n + 3)) × Bool × Bool
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 2)
    ∃ Q : I → Domain (n + 3) ≃ₗᵢ[ℝ] Domain (n + 3),
      (∀ p x, (e (Q p x)).2 = 0 ↔
        x (p.1 1) = (if p.2.1 then (1 : ℝ) else -1) * x (p.1 0) ∧
        x (p.1 2) = (if p.2.2 then (1 : ℝ) else -1) * x (p.1 0)) ∧
      ∀ x, x ∈ ⋃ p : I, {y | (e (Q p y)).2 = 0} ↔
        ∃ i j k : Fin (n + 3), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          |x j| = |x i| ∧ |x k| = |x i| := by
  classical
  intro I e
  have hExists (p : I) : ∃ Q : Domain (n + 3) ≃ₗᵢ[ℝ] Domain (n + 3),
      ∀ x, (e (Q x)).2 = 0 ↔
        x (p.1 1) = (if p.2.1 then (1 : ℝ) else -1) * x (p.1 0) ∧
        x (p.1 2) = (if p.2.2 then (1 : ℝ) else -1) * x (p.1 0) :=
    exists_coordinate_triple_tie_plane_isometry (p.1 0) (p.1 1) (p.1 2)
      (p.1.injective.ne (by decide)) (p.1.injective.ne (by decide))
      (p.1.injective.ne (by decide))
      (if p.2.1 then (1 : ℝ) else -1) (if p.2.2 then (1 : ℝ) else -1)
  choose Q hQ using hExists
  refine ⟨Q, hQ, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    obtain ⟨hj, hk⟩ := (hQ p x).mp hp
    refine ⟨p.1 0, p.1 1, p.1 2, p.1.injective.ne (by decide),
      p.1.injective.ne (by decide), p.1.injective.ne (by decide), ?_, ?_⟩
    · rw [hj, abs_mul]
      have hsign : |(if p.2.1 then (1 : ℝ) else -1)| = 1 := by cases p.2.1 <;> norm_num
      rw [hsign, one_mul]
    · rw [hk, abs_mul]
      have hsign : |(if p.2.2 then (1 : ℝ) else -1)| = 1 := by cases p.2.2 <;> norm_num
      rw [hsign, one_mul]
  · rintro ⟨i, j, k, hij, hik, hjk, hj, hk⟩
    let f : Fin 3 → Fin (n + 3) := ![i, j, k]
    have hf : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [f]
    obtain ⟨s, hs⟩ := exists_bool_sign_mul_of_abs_eq hj
    obtain ⟨t, ht⟩ := exists_bool_sign_mul_of_abs_eq hk
    let p' : I := (⟨f, hf⟩, s, t)
    apply mem_iUnion.mpr
    refine ⟨p', ?_⟩
    exact (hQ p' x).mpr ⟨hs, ht⟩

end StratificationTheory
