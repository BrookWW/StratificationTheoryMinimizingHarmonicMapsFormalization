module

public import StratificationTheory.Foundation.DensityMapCongruence
public import StratificationTheory.Foundation.ZeroEnergyRigidity
public import StratificationTheory.Foundation.DensityRegularity
public import StratificationTheory.TangentMaps.CenteredConstantEnergy
public import StratificationTheory.Frozen.SingularSet
import StratificationTheory.Foundation.SmoothRepresentativeNeighborhoods
import StratificationTheory.Foundation.RegularPointNeighborhoods

/-!
# Regularity and constancy of homogeneous Sobolev maps

A globally local Sobolev map that is invariant almost everywhere under every
positive dilation and regular at the origin is almost everywhere constant.
For a nonconstant homogeneous minimizer, every point with the same density as
the origin is singular.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ContDiff

namespace StratificationTheory.TangentMaps

theorem exists_ae_eq_const_of_homogeneous_regular_origin {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (hreg : IsRegularPoint ⟨univ, isOpen_univ⟩ u ⟨0, mem_univ 0⟩) :
    ∃ c : Ambient q, u =ᵐ[volume] (fun _ => c) := by
  obtain ⟨U, haU, hU, w, hw, hwu⟩ :=
    (isRegularPoint_iff_exists_open_neighborhood ⟨univ, isOpen_univ⟩ u
      ⟨0, mem_univ 0⟩).mp hreg
  have hzero := normalizedEnergy_tendsto_zero_of_local_contDiffOn_rep hu.1
    (0 : Domain n) ⟨U, haU, hU, w, hw.of_le (by norm_num), hwu.symm⟩
  have hconstant : (fun r : PositiveRadius => (normalizedEnergy Du 0 r).toReal) =
      (fun _ => (normalizedEnergy Du 0 ⟨1, by norm_num⟩).toReal) := by
    funext r
    exact congrArg ENNReal.toReal (normalizedEnergy_eq_unit_of_ae_homogeneous hu hhom r)
  have hunit : (normalizedEnergy Du 0 ⟨1, by norm_num⟩).toReal = 0 := by
    have hlimit : Tendsto (fun r : PositiveRadius => (normalizedEnergy Du 0 r).toReal)
        atBot (𝓝 (normalizedEnergy Du 0 ⟨1, by norm_num⟩).toReal) := by
      rw [hconstant]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlimit hzero
  apply exists_ae_eq_const_of_all_centered_energies_zero hu (0 : Domain n)
  intro r
  have hreal : (normalizedEnergy Du 0 r).toReal = 0 := by
    rw [normalizedEnergy_eq_unit_of_ae_homogeneous hu hhom r, hunit]
  have hnormzero : normalizedEnergy Du 0 r = 0 := by
    rw [← ENNReal.ofReal_toReal (hu.normalizedEnergy_ne_top_ball (subset_univ _)),
      hreal, ENNReal.ofReal_zero]
  change ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
    dirichletEnergy Du (Metric.ball (0 : Domain n) r.val) = 0 at hnormzero
  exact (mul_eq_zero.mp hnormzero).resolve_left (normalizationFactor_ne_zero r)

theorem not_isRegularPoint_origin_of_ae_homogeneous_nonconstant {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (hnonconstant : ¬ ∃ c : Ambient q, u =ᵐ[volume] (fun _ => c)) :
    ¬ IsRegularPoint ⟨univ, isOpen_univ⟩ u ⟨0, mem_univ 0⟩ := by
  intro hreg
  exact hnonconstant (exists_ae_eq_const_of_homogeneous_regular_origin hu hhom hreg)

theorem singular_of_ae_homogeneous_nonconstant_and_density_eq_origin {n q : ℕ}
    (hn : 2 ≤ n) {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (hnonconstant : ¬ ∃ c : Ambient q, u =ᵐ[volume] (fun _ => c))
    (y : Domain n)
    (hy : density hn hmin hu hN ⟨y, mem_univ y⟩ = density hn hmin hu hN ⟨0, mem_univ 0⟩) :
    ⟨y, mem_univ y⟩ ∈ singularSet ⟨univ, isOpen_univ⟩ u := by
  intro hreg
  have hzero : density hn hmin hu hN ⟨0, mem_univ 0⟩ = 0 :=
    hy.symm.trans (density_eq_zero_of_isRegularPoint hn hmin hu hN ⟨y, mem_univ y⟩ hreg)
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_density_threshold_for_isRegularPoint hn N
  have hreg0 : IsRegularPoint ⟨univ, isOpen_univ⟩ u ⟨0, mem_univ 0⟩ := by
    apply hsmall ⟨univ, isOpen_univ⟩ u Du hmin hu hN ⟨0, mem_univ 0⟩
    rw [hzero]
    exact hε
  exact not_isRegularPoint_origin_of_ae_homogeneous_nonconstant hu hhom hnonconstant hreg0

end StratificationTheory.TangentMaps
