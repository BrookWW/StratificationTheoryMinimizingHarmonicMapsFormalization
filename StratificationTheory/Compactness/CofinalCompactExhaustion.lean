module

public import HarmonicMaps.Sobolev
public import Mathlib.Topology.Compactness.SigmaCompact

public section

open HarmonicMaps Set

namespace StratificationTheory.Compactness

/-- Every open Euclidean domain has an increasing compact exhaustion cofinal
among all compact subsets contained in the domain. -/
theorem exists_cofinal_compact_exhaustion_openDomain {n : ℕ} (Ω : OpenDomain n) :
    ∃ K : ℕ → Set (Domain n),
      (∀ j, IsCompact (K j)) ∧ (∀ j, K j ⊆ Ω.val) ∧ Monotone K ∧
      (⋃ j, K j) = Ω.val ∧
      ∀ T : Set (Domain n), IsCompact T → T ⊆ Ω.val → ∃ j, T ⊆ K j := by
  letI : LocallyCompactSpace Ω.val := Ω.property.locallyCompactSpace
  let e := CompactExhaustion.choice Ω.val
  let K : ℕ → Set (Domain n) := fun j => Subtype.val '' e j
  have hK (j : ℕ) : IsCompact (K j) := (e.isCompact j).image continuous_subtype_val
  have hKΩ (j : ℕ) : K j ⊆ Ω.val := by
    rintro _ ⟨x, _hx, rfl⟩
    exact x.property
  refine ⟨K, hK, hKΩ, ?_, ?_, ?_⟩
  · intro i j hij
    exact image_mono (e.subset hij)
  · simp only [K, ← image_iUnion, e.iUnion_eq, image_univ, Subtype.range_coe]
  · intro T hT hTΩ
    have hT' : IsCompact (Subtype.val ⁻¹' T : Set Ω.val) := by
      apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_iff.mpr
      rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hTΩ]
      exact hT
    obtain ⟨j, hj⟩ := e.exists_superset_of_isCompact hT'
    refine ⟨j, ?_⟩
    intro x hx
    exact ⟨⟨x, hTΩ hx⟩, hj hx, rfl⟩

end StratificationTheory.Compactness
