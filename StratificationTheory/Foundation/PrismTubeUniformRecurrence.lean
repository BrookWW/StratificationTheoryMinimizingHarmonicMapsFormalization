module
public import StratificationTheory.Foundation.PrismEnergyRecurrence

/-!
# A uniform original-edge tube bound through every prism rank

The actual rank-one tube bound and the finite sorted-facet recursion give
one dimension-only multiple of that same original bound at every positive
rank. The recursive estimate uses no new geometric or analytic premise.
-/

public section
open scoped BigOperators
namespace StratificationTheory

/-- The genuine positive-rank facet recursion propagates a single uniform
original-edge tube bound with an explicit dimension-only coefficient. -/
theorem prism_tube_uniform_recurrence {Cell : ℕ → Type*}
    (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
    (Tube : (r : ℕ) → Cell r → ℝ) (B : ℝ)
    (hBase : ∀ p : Cell 1, Tube 1 p ≤ B)
    (hStep : ∀ (r : ℕ) (p : Cell (r + 2)), Tube (r + 2) p ≤
      ∑ i : Fin (r + 2), ∑ side : Bool, Tube (r + 1) (child (r + 1) p i side)) :
    ∀ (r : ℕ) (p : Cell (r + 1)), Tube (r + 1) p ≤
      (2 : ℝ) ^ r * ((r + 1).factorial : ℝ) * B := by
  intro r
  induction r with
  | zero =>
      intro p
      simpa only [Nat.zero_add, pow_zero, Nat.factorial_one, Nat.cast_one, one_mul] using hBase p
  | succ r ih =>
      intro p
      calc
        Tube (r + 2) p ≤ ∑ i : Fin (r + 2), ∑ side : Bool,
            Tube (r + 1) (child (r + 1) p i side) := hStep r p
        _ ≤ ∑ _i : Fin (r + 2), ∑ _side : Bool,
            (2 : ℝ) ^ r * ((r + 1).factorial : ℝ) * B := by
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun side _ => ih _
        _ = (2 : ℝ) ^ (r + 1) * ((r + 2).factorial : ℝ) * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
          have hFact : (r + 2).factorial = (r + 2) * (r + 1).factorial := Nat.factorial_succ (r + 1)
          rw [pow_succ, hFact, Nat.cast_mul]
          ring

end StratificationTheory
