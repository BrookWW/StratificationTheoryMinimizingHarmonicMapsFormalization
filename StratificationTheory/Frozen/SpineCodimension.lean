-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SpineCharacterization
public import StratificationTheory.Frozen.SingularSetNull
public import Mathlib.Analysis.InnerProductSpace.Subspace


import StratificationTheory.Providers.SpineCodimension

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory

/-- A nonconstant homogeneous minimizer has its same characterized spine
inside its actual singular image, with real vector-space dimension at most n-3. -/
theorem spine_singular_and_finrank_le {n q : ℕ} (hn : 3 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (hnonconstant : ¬ ∃ c : Ambient q, u =ᵐ[volume] (fun x => c)) :
    let hn₂ : 2 ≤ n := Nat.le_of_succ_le hn
    ((spine hn₂ hmin hu hN hhom : Set (Domain n)) ⊆
      Subtype.val '' singularSet ⟨univ, isOpen_univ⟩ u) ∧
      Module.finrank ℝ (spine hn₂ hmin hu hN hhom) ≤ n - 3 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SpineCodimension.result hn hmin hu hN hhom hnonconstant
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
