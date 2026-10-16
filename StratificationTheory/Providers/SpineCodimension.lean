module

public import StratificationTheory.Frozen.SpineCharacterization
public import StratificationTheory.Frozen.SingularSetNull
public import Mathlib.Analysis.InnerProductSpace.Subspace

import StratificationTheory.TangentMaps.HomogeneousRegularRigidity
import StratificationTheory.MeasureTheory.SubspaceHausdorff

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory.Providers.SpineCodimension

/-- A nonconstant homogeneous minimizer has its same characterized spine
inside its actual singular image, with real vector-space dimension at most n-3. -/
theorem result {n q : ℕ} (hn : 3 ≤ n)
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
      Module.finrank ℝ (spine hn₂ hmin hu hN hhom) ≤ n - 3 := by
  dsimp only
  let hn₂ : 2 ≤ n := Nat.le_of_succ_le hn
  have hchar := spine_characterization hn₂ hmin hu hN hhom
  have hsubset : (spine hn₂ hmin hu hN hhom : Set (Domain n)) ⊆
      Subtype.val '' singularSet ⟨univ, isOpen_univ⟩ u := by
    intro y hy
    have hySing := TangentMaps.singular_of_ae_homogeneous_nonconstant_and_density_eq_origin
      hn₂ hmin hu hN hhom hnonconstant y ((hchar.1 y).mp hy)
    exact ⟨⟨y, mem_univ y⟩, hySing, rfl⟩
  exact ⟨hsubset, finrank_le_of_subspace_subset_hausdorff_null hn
    (spine hn₂ hmin hu hN hhom) _ hsubset
    (singularSet_hausdorffMeasure_zero hn₂ hmin hu hN)⟩

end StratificationTheory.Providers.SpineCodimension
