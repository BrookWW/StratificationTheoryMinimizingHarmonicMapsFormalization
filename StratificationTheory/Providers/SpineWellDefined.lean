module

public import HarmonicMaps.Minimizer
public import StratificationTheory.Frozen.DensityCharacterization
public import Mathlib.Analysis.InnerProductSpace.Subspace

import StratificationTheory.TangentMaps.DensityEqualitySubspace
import StratificationTheory.TangentMaps.DensityEqualityInvariance
import StratificationTheory.TangentMaps.CenteredConstantEnergy
import StratificationTheory.Foundation.DensityMapCongruence

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory.Providers.SpineWellDefined

/-- A globally local homogeneous minimizer determines one real subspace with
its full density-equality carrier, global density maximum and translation
invariance of the same almost-everywhere map class. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u) :
    ∃! V : Subspace ℝ (Domain n),
      (∀ y : Domain n, y ∈ V ↔
        density hn hmin hu hN ⟨y, mem_univ y⟩ = density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
      (∀ y : Domain n,
        density hn hmin hu hN ⟨y, mem_univ y⟩ ≤ density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
      ∀ y : Domain n, y ∈ V → (fun x => u (x + y)) =ᵐ[volume] u := by
  let θ : ℝ := (normalizedEnergy Du 0 ⟨1, by norm_num⟩).toReal
  have henergy (r : PositiveRadius) : (normalizedEnergy Du 0 r).toReal = θ := by
    exact congrArg ENNReal.toReal (normalizedEnergy_eq_unit_of_ae_homogeneous hu hhom r)
  obtain ⟨V, hV, huniq⟩ := TangentMaps.existsUnique_density_equality_subspace
    hn hmin hu hN θ henergy
  have hzero := TangentMaps.density_origin_eq_constant hn hmin hu hN θ henergy
  refine ⟨V, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro y
    rw [hzero]
    exact hV y
  · intro y
    rw [hzero]
    exact TangentMaps.density_le_origin_constant hn hmin hu hN θ henergy y
  · intro y hy
    simpa only [one_smul] using
      TangentMaps.ae_eq_translate_smul_of_density_eq_origin_constant
        hn hmin hu hN θ henergy y ((hV y).mp hy) 1
  · intro W hW
    apply huniq W
    intro y
    simpa only [hzero] using hW.1 y

end StratificationTheory.Providers.SpineWellDefined
