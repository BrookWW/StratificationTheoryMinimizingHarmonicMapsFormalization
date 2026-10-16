module

public import StratificationTheory.TangentMaps.CenteredConstantEnergy
public import StratificationTheory.Foundation.AffineAEInvariance

/-!
# Density equality and centered invariance

Constant normalized energy at the origin bounds energy at every other center.
Equality of density with that constant forces constant energy at the new
center. The actual monotonicity and Sobolev radial rigidity theorems then
produce centered homogeneity and translation invariance.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StratificationTheory.TangentMaps

theorem normalizedEnergy_eq_origin_constant_of_density_eq {n q : ℕ}
    (hn : 2 ≤ n) {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (hy : density hn hmin hu hN ⟨y, mem_univ y⟩ = θ)
    (r : PositiveRadius) :
    (normalizedEnergy Du y r).toReal = θ := by
  apply le_antisymm (normalizedEnergy_toReal_le_origin_constant hn hmin hu hN θ henergy y r)
  rw [← hy]
  exact density_le_normalizedEnergy_toReal hn hmin hu hN ⟨y, mem_univ y⟩ r (subset_univ _)

theorem ae_eq_centered_dilation_of_density_eq_origin_constant {n q : ℕ}
    (hn : 2 ≤ n) {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (hy : density hn hmin hu hN ⟨y, mem_univ y⟩ = θ)
    {l : ℝ} (hl : 0 < l) :
    (fun x => u (y + l • (x - y))) =ᵐ[volume] u := by
  exact hmin.ae_eq_rescale_of_constant_energy hn hu hN y θ
    (normalizedEnergy_eq_origin_constant_of_density_eq hn hmin hu hN θ henergy y hy) hl

theorem ae_eq_translate_smul_of_density_eq_origin_constant {n q : ℕ}
    (hn : 2 ≤ n) {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (hy : density hn hmin hu hN ⟨y, mem_univ y⟩ = θ)
    (t : ℝ) :
    (fun x => u (x + t • y)) =ᵐ[volume] u := by
  apply ae_eq_translate_smul_of_all_centered_dilations y ?_ ?_ t
  · intro l hl
    have h := hmin.ae_eq_rescale_of_constant_energy hn hu hN (0 : Domain n) θ henergy hl
    simpa only [zero_add, sub_zero] using h
  · intro l hl
    exact ae_eq_centered_dilation_of_density_eq_origin_constant hn hmin hu hN θ henergy y hy hl

end StratificationTheory.TangentMaps
