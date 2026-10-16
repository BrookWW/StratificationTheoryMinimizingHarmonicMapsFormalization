module

public import StratificationTheory.Foundation.CubicalSignedPairFrame
public import StratificationTheory.Foundation.CubicalSignedPermutations

public section

open HarmonicMaps

namespace StratificationTheory

/-- The finite literal signed-permutation family contains a correctly
oriented frame for every ordered pair of distinct signed cube facets. -/
theorem exists_cubical_signed_pair_permutation {n : ℕ}
    (i j : Fin ((n + 1) + 1)) (hij : i ≠ j) (positiveI positiveJ : Bool) :
    ∃ (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool),
      p (Fin.last (n + 1)) = i ∧ p (Fin.last n).castSucc = j ∧
      s (Fin.last (n + 1)) = positiveI ∧ s (Fin.last n).castSucc = positiveJ ∧
      ∀ x,
        (if positiveI then (cubicalSignedPermutation ((n + 1) + 1) p s x) i
          else -(cubicalSignedPermutation ((n + 1) + 1) p s x) i) = x (Fin.last (n + 1)) ∧
        (if positiveJ then (cubicalSignedPermutation ((n + 1) + 1) p s x) j
          else -(cubicalSignedPermutation ((n + 1) + 1) p s x) j) = x (Fin.last n).castSucc := by
  obtain ⟨p, s, A, hpl, hpm, hsl, hsm, hApply, _hMax, hNormal⟩ :=
    exists_cubical_signed_pair_frame i j hij positiveI positiveJ
  have hA : A = cubicalSignedPermutation ((n + 1) + 1) p s := by
    apply LinearIsometryEquiv.ext
    intro x
    ext k
    obtain ⟨l, rfl⟩ := p.surjective k
    exact (hApply x l).trans (cubicalSignedPermutation_apply p s x l).symm
  refine ⟨p, s, hpl, hpm, hsl, hsm, ?_⟩
  simpa only [hA] using hNormal

end StratificationTheory
