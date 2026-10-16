module

public import StratificationTheory.Foundation.CubicalSignedPermutations
public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps

namespace StratificationTheory

/-- Composition remains in the same finite literal signed-permutation
family, with its exact source sign formula. -/
theorem cubicalSignedPermutation_compose {d : ℕ}
    (p₀ p₁ : Equiv.Perm (Fin d)) (s₀ s₁ : Fin d → Bool) :
    (cubicalSignedPermutation d p₀ s₀).trans (cubicalSignedPermutation d p₁ s₁) =
      cubicalSignedPermutation d (p₀.trans p₁)
        (fun k => if s₀ k then s₁ (p₀ k) else !(s₁ (p₀ k))) := by
  apply LinearIsometryEquiv.ext
  intro x
  ext l
  obtain ⟨k, rfl⟩ := (p₀.trans p₁).surjective l
  change cubicalSignedPermutation d p₁ s₁ (cubicalSignedPermutation d p₀ s₀ x) (p₁ (p₀ k)) = _
  rw [cubicalSignedPermutation_apply, cubicalSignedPermutation_apply,
    cubicalSignedPermutation_apply]
  cases s₀ k <;> cases s₁ (p₀ k) <;> simp

/-- The canonical signed-face chart is an actual member of the same finite
ambient family, including its complete normal reflection. -/
theorem cubicalSignedFaceIsometry_as_signedPermutation {n : ℕ}
    (i : Fin (n + 1)) (positive : Bool) :
    cubicalSignedFaceIsometry n i positive =
      cubicalSignedPermutation (n + 1) (Equiv.swap (Fin.last n) i)
        (fun k => if k = Fin.last n then positive else true) := by
  apply LinearIsometryEquiv.ext
  intro x
  ext l
  obtain ⟨k, rfl⟩ := (Equiv.swap (Fin.last n) i).surjective l
  rw [cubicalSignedFaceIsometry_apply, cubicalSignedPermutation_apply]
  by_cases hk : k = Fin.last n <;> simp [hk]

end StratificationTheory
