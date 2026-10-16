module

public import StratificationTheory.TangentMaps.DensityEqualityInvariance
public import StratificationTheory.Foundation.DensityMapCongruence

/-!
# The linear subspace determined by density equality

For a global local minimizer with constant normalized energy at the origin,
density equality is preserved by addition and every real scalar multiple.
It determines exactly one real linear subspace, whose directions preserve
the actual map almost everywhere.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StratificationTheory.TangentMaps

theorem density_eq_origin_constant_of_ae_translate {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (hy : (fun x => u (x + y)) =ᵐ[volume] u) :
    density hn hmin hu hN ⟨y, mem_univ y⟩ = θ := by
  have hshift := density_eq_of_ae_translate hn hmin hu hN y hy (0 : Domain n)
  simpa only [zero_add] using hshift.trans
    (density_origin_eq_constant hn hmin hu hN θ henergy)

theorem density_eq_origin_constant_add {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y z : Domain n) (hy : density hn hmin hu hN ⟨y, mem_univ y⟩ = θ)
    (hz : density hn hmin hu hN ⟨z, mem_univ z⟩ = θ) :
    density hn hmin hu hN ⟨y + z, mem_univ _⟩ = θ := by
  have hty : (fun x => u (x + y)) =ᵐ[volume] u := by
    simpa only [one_smul] using
      ae_eq_translate_smul_of_density_eq_origin_constant hn hmin hu hN θ henergy y hy 1
  have htz : (fun x => u (x + z)) =ᵐ[volume] u := by
    simpa only [one_smul] using
      ae_eq_translate_smul_of_density_eq_origin_constant hn hmin hu hN θ henergy z hz 1
  exact density_eq_origin_constant_of_ae_translate hn hmin hu hN θ henergy (y + z)
    (ae_eq_translate_add y z hty htz)

theorem density_eq_origin_constant_smul {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (hy : density hn hmin hu hN ⟨y, mem_univ y⟩ = θ) (t : ℝ) :
    density hn hmin hu hN ⟨t • y, mem_univ _⟩ = θ := by
  exact density_eq_origin_constant_of_ae_translate hn hmin hu hN θ henergy (t • y)
    (ae_eq_translate_smul_of_density_eq_origin_constant hn hmin hu hN θ henergy y hy t)

theorem existsUnique_density_equality_subspace {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ) :
    ∃! V : Subspace ℝ (Domain n),
      ∀ y : Domain n, y ∈ V ↔ density hn hmin hu hN ⟨y, mem_univ y⟩ = θ := by
  let V : Subspace ℝ (Domain n) := {
    carrier := {y | density hn hmin hu hN ⟨y, mem_univ y⟩ = θ}
    zero_mem' := density_origin_eq_constant hn hmin hu hN θ henergy
    add_mem' := fun hy hz => density_eq_origin_constant_add hn hmin hu hN θ henergy _ _ hy hz
    smul_mem' := fun t y hy => density_eq_origin_constant_smul hn hmin hu hN θ henergy y hy t }
  refine ⟨V, (fun _ => Iff.rfl), ?_⟩
  intro W hW
  apply SetLike.ext
  intro y
  exact hW y

end StratificationTheory.TangentMaps
