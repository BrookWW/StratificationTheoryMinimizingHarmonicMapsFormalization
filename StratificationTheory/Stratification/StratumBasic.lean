module

public import StratificationTheory.Frozen.SingularStratum
public import StratificationTheory.TangentMaps.TangentNonconstant

public section
open HarmonicMaps MeasureTheory Metric Set Module
namespace StratificationTheory

/-- Membership quantifies over every raw tangent and every proof of its
derived qualifications, always using the same characterized spine. -/
theorem mem_singularStratum_iff {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) (j : ℕ) (a : Ω.val) :
    a ∈ singularStratum hn N Ω u Du hu hTarget hMinimizer j ↔
      a ∈ singularSet Ω u ∧
      ∀ (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
        IsTangentAt u Du a.val φ Dφ →
        ∀ (hMinφ : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ)
          (hφ : MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ)
          (hTφ : TakesValuesIn N ⟨univ, isOpen_univ⟩ φ)
          (hHom : ∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ),
          finrank ℝ (spine hn hMinφ hφ hTφ hHom) ≤ j := by
  constructor
  · intro ha
    refine ⟨ha.1, ?_⟩
    intro φ Dφ hT hMinφ hφ hTφ hHom
    exact ha.2 φ Dφ hT
  · rintro ⟨hSing, hRank⟩
    refine ⟨hSing, ?_⟩
    intro φ Dφ hT
    let Q := IsTangentAt.qualification hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT
    exact hRank φ Dφ hT Q.2.2.1 Q.1 Q.2.1 Q.2.2.2.2

theorem singularStratum_mono {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) {i j : ℕ} (hij : i ≤ j) :
    singularStratum hn N Ω u Du hu hTarget hMinimizer i ⊆
      singularStratum hn N Ω u Du hu hTarget hMinimizer j := by
  intro a ha
  exact ⟨ha.1, fun φ Dφ hT => (ha.2 φ Dφ hT).trans hij⟩

/-- The codimension bound for every actual tangent identifies each maximal
stratum with the full singular set in dimensions at least three. -/
theorem singularStratum_eq_singularSet_of_index_ge {n q : ℕ} (hn : 3 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) (j : ℕ) (hj : n - 3 ≤ j) :
    singularStratum (Nat.le_of_succ_le hn) N Ω u Du hu hTarget hMinimizer j =
      singularSet Ω u := by
  apply Set.ext
  intro a
  constructor
  · exact fun ha => ha.1
  · intro ha
    refine ⟨ha, ?_⟩
    intro φ Dφ hT
    exact (IsTangentAt.spine_singular_and_finrank_le_of_singular hn N Ω u Du
      hu hTarget hMinimizer a φ Dφ hT ha).2.trans hj

end StratificationTheory
