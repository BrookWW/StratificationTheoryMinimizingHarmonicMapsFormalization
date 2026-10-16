module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import StratificationTheory.Foundation.CubicalConeGeometry

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- The actual signed face chart sends exactly its strict dominant-coordinate
cone to the standard positive-height face cone. -/
theorem cubicalSignedFaceIsometry_strict_cone_iff {n : ℕ}
    (i : Fin (n + 1)) (positive : Bool) (x : Domain (n + 1)) :
    let Q := cubicalSignedFaceIsometry n i positive
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let h := if positive then x i else -x i
    ((e (Q.symm x)).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k : Fin n, |(e (Q.symm x)).1 k| < (e (Q.symm x)).2 0) ↔
      h ∈ Ioo (0 : ℝ) 1 ∧ ∀ j : Fin (n + 1), j ≠ i → |x j| < h := by
  intro Q e h
  let p := Equiv.swap (Fin.last n) i
  have hN : (e (Q.symm x)).2 0 = h := by
    change Q.symm x (Fin.last n) = _
    simpa only [ite_true] using cubicalSignedFaceIsometry_symm_apply i positive x (Fin.last n)
  have hA (k : Fin n) : |(e (Q.symm x)).1 k| = |x (p k.castSucc)| := by
    change |Q.symm x k.castSucc| = _
    rw [cubicalSignedFaceIsometry_symm_apply, if_neg (Fin.castSucc_ne_last k)]
  constructor
  · intro hx
    refine ⟨by simpa only [hN] using hx.1, ?_⟩
    have hAll (l : Fin (n + 1)) : l ≠ Fin.last n → |Q.symm x l| < h := by
      refine Fin.lastCases (fun hl => False.elim (hl rfl)) (fun k _ => ?_) l
      change |(e (Q.symm x)).1 k| < h
      simpa only [hN] using hx.2 k
    intro j hji
    have hpj : p j ≠ Fin.last n := by
      intro hp
      have hj : j = i := by
        have hh := congrArg p hp
        simpa only [p, Equiv.swap_apply_self, Equiv.swap_apply_left] using hh
      exact hji hj
    have hh := hAll (p j) hpj
    rw [cubicalSignedFaceIsometry_symm_apply, if_neg hpj] at hh
    simpa only [p, Equiv.swap_apply_self] using hh
  · rintro ⟨hh, hother⟩
    refine ⟨by simpa only [hN] using hh, ?_⟩
    intro k
    have hpki : p k.castSucc ≠ i := by
      intro hk
      have hkl : k.castSucc = Fin.last n := p.injective
        (hk.trans (Equiv.swap_apply_left (Fin.last n) i).symm)
      exact Fin.castSucc_ne_last k hkl
    rw [hA, hN]
    exact hother _ hpki

/-- On each signed cone, the literal maximum-coordinate radial retraction
is exactly the corresponding unit-face chart with inverse-height spatial
coordinates. -/
theorem cubical_radial_retraction_signed_face {n : ℕ}
    (i : Fin (n + 1)) (positive : Bool) (x : Domain (n + 1))
    (hpos : 0 < (if positive then x i else -x i))
    (hother : ∀ j : Fin (n + 1), j ≠ i → |x j| < (if positive then x i else -x i)) :
    let Q := cubicalSignedFaceIsometry n i positive
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let h := if positive then x i else -x i
    ‖WithLp.ofLp x‖ = h ∧
      ‖WithLp.ofLp x‖⁻¹ • x =
        Q (e.symm (h⁻¹ • (e (Q.symm x)).1, EuclideanSpace.single (0 : Fin 1) 1)) := by
  intro Q e h
  have hAbs : |x i| = h := by
    dsimp only [h]
    cases positive
    · simpa only [Bool.false_eq_true, ite_false, abs_neg] using abs_of_pos hpos
    · exact abs_of_pos hpos
  have hNorm : ‖WithLp.ofLp x‖ = h := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hpos.le).mpr
      intro j
      rw [Real.norm_eq_abs]
      by_cases hji : j = i
      · simpa only [hji, hAbs] using le_rfl
      · exact (hother j hji).le
    · have hh := norm_le_pi_norm (WithLp.ofLp x) i
      simpa only [Real.norm_eq_abs, hAbs] using hh
  have hN : (e (Q.symm x)).2 0 = h := by
    change Q.symm x (Fin.last n) = _
    simpa only [ite_true] using cubicalSignedFaceIsometry_symm_apply i positive x (Fin.last n)
  refine ⟨hNorm, ?_⟩
  rw [hNorm]
  calc
    h⁻¹ • x = Q (h⁻¹ • Q.symm x) := by rw [Q.map_smul, Q.apply_symm_apply]
    _ = _ := by
      apply congrArg Q
      apply e.injective
      rw [e.map_smul, e.apply_symm_apply]
      apply Prod.ext
      · rfl
      · ext l
        have hl : l = 0 := Subsingleton.elim _ _
        subst l
        simp only [Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, hN,
          PiLp.single_apply, ite_true]
        exact inv_mul_cancel₀ (ne_of_gt (show 0 < h from hpos))

end StratificationTheory
