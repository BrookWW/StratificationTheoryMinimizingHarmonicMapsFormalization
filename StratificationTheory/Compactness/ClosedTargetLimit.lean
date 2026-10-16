module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import HarmonicMaps.Minimizer
public import Mathlib.Topology.Compactness.SigmaCompact

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StratificationTheory.Compactness

/-- Almost-everywhere membership in a closed target is preserved by strong
L2 convergence. The almost-everywhere subsequence is used only in the proof. -/
theorem ae_mem_closed_of_L2_limit {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f : ℕ → α → E} {u : α → E} {S : Set E}
    (hS : IsClosed S) (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hTarget : ∀ k, ∀ᵐ x ∂μ, f k x ∈ S)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, u x ∈ S := by
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ENNReal) ≠ 0)
    (fun k => (hf k).aestronglyMeasurable) hu.aestronglyMeasurable hconv
  obtain ⟨κ, _hκ, hAE⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hAE, ae_all_iff.mpr (fun k => hTarget (κ k))] with x hx hTx
  exact hS.mem_of_tendsto hx (Eventually.of_forall hTx)

/-- The imported target-valuedness predicate is closed under strong L2
convergence on the entire domain, including domains of infinite volume. -/
theorem takesValuesIn_of_L2_limit {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict Ω.val))
    (hu : MemLp u 2 (volume.restrict Ω.val))
    (hTarget : ∀ k, TakesValuesIn N Ω (f k))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict Ω.val))
      atTop (𝓝 0)) : TakesValuesIn N Ω u :=
  ae_mem_closed_of_L2_limit N.isClosed hf hu hTarget hconv

/-- Strong L2 convergence on every compact subset of an arbitrary open domain
preserves actual almost-everywhere target membership on the whole domain. -/
theorem takesValuesIn_of_local_L2_limit {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (hf : ∀ k, LocallyMemL2 Ω (f k))
    (hu : LocallyMemL2 Ω u)
    (hTarget : ∀ k, TakesValuesIn N Ω (f k))
    (hconv : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict K)) atTop (𝓝 0)) :
    TakesValuesIn N Ω u := by
  letI : LocallyCompactSpace Ω.val := Ω.property.locallyCompactSpace
  have hs : IsSigmaCompact Ω.val :=
    isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hs
  change ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet
  rw [← hcover]
  apply (ae_restrict_iUnion_iff K _).mpr
  intro j
  have hKΩ : K j ⊆ Ω.val := hcover ▸ subset_iUnion K j
  exact ae_mem_closed_of_L2_limit N.isClosed
    (fun k => hf k (K j) (hK j) hKΩ) (hu (K j) (hK j) hKΩ)
    (fun k => ae_restrict_of_ae_restrict_of_subset hKΩ (hTarget k))
    (hconv (K j) (hK j) hKΩ)

end StratificationTheory.Compactness
