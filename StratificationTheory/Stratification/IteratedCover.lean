/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import HarmonicMaps.Sobolev

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Iteration of finite covers with centers in the set

A finite one-step covering rule with a uniform contraction and cardinal
bound produces actual finite centers at every generation. The centers remain
in the original set, the generation radius is the prescribed geometric
radius, and taking finite unions does not increase the cardinal bound.
The one-step rule is an explicit premise of this internal iteration lemma.
-/

public section

open Metric Set
open scoped BigOperators

namespace StratificationTheory

/-- An actual finite covering rule can be iterated at every admissible
smaller radius. All three generation properties concern the same Finset. -/
theorem exists_iterated_finset_cover {X : Type*} [PseudoMetricSpace X]
    (A : Set X) (σ r₀ : ℝ) (K : ℕ) (hσ : 0 < σ) (hσone : σ < 1)
    (hstep : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset X, (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < σ * r) ∧ C.card ≤ K)
    (a : X) (ha : a ∈ A) (R : ℝ) (hR : 0 < R) (hRr₀ : R ≤ r₀) :
    ∀ k : ℕ, ∃ C : Finset X, (∀ c ∈ C, c ∈ A) ∧
      (∀ x ∈ A ∩ ball a R, ∃ c ∈ C, dist x c < σ ^ k * R) ∧ C.card ≤ K ^ k := by
  classical
  intro k
  induction k with
  | zero =>
    refine ⟨{a}, ?_, ?_, ?_⟩
    · intro c hc
      exact (Finset.mem_singleton.mp hc) ▸ ha
    · intro x hx
      exact ⟨a, Finset.mem_singleton_self a, by
        simpa only [pow_zero, one_mul] using mem_ball.mp hx.2⟩
    · simp only [Finset.card_singleton, pow_zero, le_refl]
  | succ k ih =>
    obtain ⟨C, hCA, hCcover, hCcard⟩ := ih
    have hscale : 0 < σ ^ k * R := mul_pos (pow_pos hσ k) hR
    have hscalesmall : σ ^ k * R ≤ r₀ := by
      calc
        σ ^ k * R ≤ 1 * R :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hσ.le hσone.le) hR.le
        _ = R := one_mul R
        _ ≤ r₀ := hRr₀
    have hchildren (p : C) : ∃ D : Finset X, (∀ c ∈ D, c ∈ A) ∧
        (∀ x ∈ A ∩ ball p.val (σ ^ k * R), ∃ c ∈ D, dist x c < σ * (σ ^ k * R)) ∧
        D.card ≤ K := hstep p.val (hCA p.val p.property) _ hscale hscalesmall
    choose D hDA hDcover hDcard using hchildren
    let children : Finset X := Finset.univ.biUnion D
    have hnextscale : σ * (σ ^ k * R) = σ ^ (k + 1) * R := by
      rw [pow_succ]
      ring
    refine ⟨children, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨p, _hp, hcD⟩ := Finset.mem_biUnion.mp hc
      exact hDA p c hcD
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := hCcover x hx
      let p' : C := ⟨p, hp⟩
      obtain ⟨c, hc, hxc⟩ := hDcover p' x ⟨hx.1, hxp⟩
      refine ⟨c, Finset.mem_biUnion.mpr ⟨p', Finset.mem_univ _, hc⟩, ?_⟩
      rw [← hnextscale]
      exact hxc
    · calc
        children.card ≤ ∑ p : C, (D p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p : C, K := Finset.sum_le_sum (fun p _ => hDcard p)
        _ = C.card * K := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
            Nat.cast_id]
        _ ≤ K ^ k * K := Nat.mul_le_mul_right K hCcard
        _ = K ^ (k + 1) := (pow_succ K k).symm

end StratificationTheory
