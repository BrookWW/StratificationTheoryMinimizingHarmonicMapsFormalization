module

public import Mathlib.Logic.Function.Basic

public section

namespace StratificationTheory

/-- Actual two-rank extensions generate one coherent family. Each chosen
successor retains the preceding rank exactly, so all adjacent relations
concern the same global family rather than independent rankwise choices. -/
theorem exists_coherent_two_step_family {A : Nat → Type*}
    (R : (n : Nat) → A n → A (n + 1) → Prop)
    (a₀ : A 0) (a₁ : A 1) (hBase : R 0 a₀ a₁)
    (hStep : ∀ (n : Nat) (a : A n) (b : A (n + 1)), R n a b →
      ∃ c : A (n + 2), R (n + 1) b c) :
    ∃ f : (n : Nat) → A n,
      f 0 = a₀ ∧ f 1 = a₁ ∧ ∀ n, R n (f n) (f (n + 1)) := by
  classical
  let X := fun n : Nat => {p : A n × A (n + 1) // R n p.1 p.2}
  let advance : (n : Nat) → X n → X (n + 1) := fun n x =>
    ⟨(x.val.2, (hStep n x.val.1 x.val.2 x.property).choose),
      (hStep n x.val.1 x.val.2 x.property).choose_spec⟩
  let seq : (n : Nat) → X n := Nat.rec ⟨(a₀, a₁), hBase⟩ advance
  let f : (n : Nat) → A n := fun n => (seq n).val.1
  have hLink (n : Nat) : (seq (n + 1)).val.1 = (seq n).val.2 := rfl
  refine ⟨f, rfl, rfl, ?_⟩
  intro n
  change R n (seq n).val.1 (seq (n + 1)).val.1
  rw [hLink]
  exact (seq n).property

end StratificationTheory
