module

public import StratificationTheory.Stratification.SpineConcentration
public import StratificationTheory.Stratification.ConcentrationDistanceScale

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- The same source radius and density tolerance give actual strict
approximation by an affine j-plane in the original physical coordinates. -/
theorem exists_affine_spine_concentration_at_stratum_point {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (_hSingular : a ∈ singularSet Ω u) (j : ℕ) (hj : j ≤ n)
    (hRank : ∀ (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      IsTangentAt u Du a.val φ Dφ →
      ∀ (hMinφ : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ)
        (hφ : MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ)
        (hTφ : TakesValuesIn N ⟨univ, isOpen_univ⟩ φ)
        (hHom : ∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ),
        Module.finrank ℝ (spine hn hMinφ hφ hTφ hHom) ≤ j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : PositiveRadius, ρ.val ≤ ε →
      closedBall a.val ρ.val ⊆ Ω.val →
      ∃ L : Subspace ℝ (Domain n), Module.finrank ℝ L = j ∧
        ∀ x : Ω.val, x.val ∈ ball a.val ρ.val →
          density hn hMinimizer hu hTarget a - ε ≤ density hn hMinimizer hu hTarget x →
          infDist x.val ((fun v : Domain n => a.val + v) '' (L : Set (Domain n))) < δ * ρ.val := by
  obtain ⟨ε, hε, hConcentration⟩ := exists_spine_concentration_at_stratum_point hn N Ω u Du
    hu hTarget hMinimizer a _hSingular j hj hRank δ hδ
  refine ⟨ε, hε, ?_⟩
  intro ρ hρε hClosed
  obtain ⟨L, hL, hNear⟩ := hConcentration ρ hρε hClosed
  refine ⟨L, hL, ?_⟩
  intro x hx hDensity
  exact (normalized_subspace_infDist_lt_iff L a.val x.val ρ.property).mp (hNear x hx hDensity)

end StratificationTheory
