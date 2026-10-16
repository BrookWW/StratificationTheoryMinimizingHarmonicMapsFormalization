module

public import Mathlib.Data.Finset.Basic

public section

namespace StratificationTheory

/-- An unordered pair of distinct physical normals determines its actual
signed labels up to exchanging their order. -/
theorem signed_normal_pair_eq_iff {I : Type*} [DecidableEq I]
    (i j i' j' : I) (s t s' t' : Bool) (hij : i ≠ j) :
    ({(i, s), (j, t)} : Finset (I × Bool)) = {(i', s'), (j', t')} ↔
      ((i, s) = (i', s') ∧ (j, t) = (j', t')) ∨
      ((i, s) = (j', t') ∧ (j, t) = (i', s')) := by
  constructor
  · intro h
    have h₀ : (i, s) = (i', s') ∨ (i, s) = (j', t') := by
      have : (i, s) ∈ ({(i', s'), (j', t')} : Finset (I × Bool)) := by rw [← h]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have h₁ : (j, t) = (i', s') ∨ (j, t) = (j', t') := by
      have : (j, t) ∈ ({(i', s'), (j', t')} : Finset (I × Bool)) := by rw [← h]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases h₀ with ha | ha
    · rcases h₁ with hb | hb
      · exact False.elim (hij (congrArg Prod.fst (ha.trans hb.symm)))
      · exact Or.inl ⟨ha, hb⟩
    · rcases h₁ with hb | hb
      · exact Or.inr ⟨ha, hb⟩
      · exact False.elim (hij (congrArg Prod.fst (ha.trans hb.symm)))
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rw [ha, hb]
    · rw [ha, hb, Finset.pair_comm]

/-- Actual lower-cell keys which agree under exchanging the two distinct
signed normals descend to one lookup on unordered signed pairs. Values
away from the displayed pair carriers are unconstrained. -/
theorem exists_lookup_of_symmetric_signed_normal_keys {I L : Type*}
    [DecidableEq I] [Nonempty L]
    (key : I → Bool → I → Bool → L)
    (hSymm : ∀ i j, i ≠ j → ∀ s t, key i s j t = key j t i s) :
    ∃ lookup : Finset (I × Bool) → L,
      ∀ i j, i ≠ j → ∀ s t,
        lookup {(i, s), (j, t)} = key i s j t := by
  classical
  let Valid := fun p : Finset (I × Bool) =>
    ∃ i j : I, ∃ s t : Bool, i ≠ j ∧ p = {(i, s), (j, t)}
  let lookup := fun p : Finset (I × Bool) => if h : Valid p then
    key h.choose h.choose_spec.choose_spec.choose
      h.choose_spec.choose h.choose_spec.choose_spec.choose_spec.choose
    else Classical.arbitrary L
  refine ⟨lookup, ?_⟩
  intro i j hij s t
  have h : Valid {(i, s), (j, t)} := ⟨i, j, s, t, hij, rfl⟩
  dsimp only [lookup]
  rw [dif_pos h]
  let i' := h.choose
  let j' := h.choose_spec.choose
  let s' := h.choose_spec.choose_spec.choose
  let t' := h.choose_spec.choose_spec.choose_spec.choose
  have hij' : i' ≠ j' := h.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hPair : ({(i', s'), (j', t')} : Finset (I × Bool)) = {(i, s), (j, t)} :=
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.symm
  change key i' s' j' t' = key i s j t
  rcases (signed_normal_pair_eq_iff i' j' i j s' t' s t hij').mp hPair with
    ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hi : i' = i := congrArg Prod.fst ha
    have hs : s' = s := congrArg Prod.snd ha
    have hj : j' = j := congrArg Prod.fst hb
    have ht : t' = t := congrArg Prod.snd hb
    rw [hi, hs, hj, ht]
  · have hi : i' = j := congrArg Prod.fst ha
    have hs : s' = t := congrArg Prod.snd ha
    have hj : j' = i := congrArg Prod.fst hb
    have ht : t' = s := congrArg Prod.snd hb
    rw [hi, hs, hj, ht]
    exact hSymm j i hij.symm t s

end StratificationTheory
