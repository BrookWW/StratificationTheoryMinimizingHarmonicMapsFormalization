module

public import StratificationTheory.TangentMaps.TangentQualification
public import StratificationTheory.TangentMaps.HomogeneousRegularRigidity
public import StratificationTheory.Frozen.RegularDensity
public import StratificationTheory.Frozen.SpineCodimension
public import StratificationTheory.Foundation.RegularPointNeighborhoods
public import Mathlib.Analysis.SpecificLimits.Basic

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal ContDiff
namespace StratificationTheory

/-- For every actual tangent, source regularity is equivalent to almost
everywhere constancy of that same tangent map. -/
theorem IsTangentAt.regular_iff_ae_constant {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hT : IsTangentAt u Du a.val φ Dφ) :
    IsRegularPoint Ω u a ↔ ∃ c : Ambient q, φ =ᵐ[volume] (fun _ => c) := by
  obtain ⟨hW, hN, hMin, hEnergy, hHom⟩ :=
    IsTangentAt.qualification hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT
  have hDensity := TangentMaps.density_origin_eq_constant hn hMin hW hN
    (density hn hMinimizer hu hTarget a) hEnergy
  obtain ⟨ε, _hε, hReg⟩ := regularPoint_density_characterization hn N
  have hSource := (hReg Ω u Du hMinimizer hu hTarget a).1
  have hLimit := (hReg ⟨univ, isOpen_univ⟩ φ Dφ hMin hW hN ⟨0, mem_univ 0⟩).1
  constructor
  · intro hRegular
    have hRegφ : IsRegularPoint ⟨univ, isOpen_univ⟩ φ ⟨0, mem_univ 0⟩ :=
      hLimit.mpr (hDensity.trans (hSource.mp hRegular))
    exact TangentMaps.exists_ae_eq_const_of_homogeneous_regular_origin hW hHom hRegφ
  · rintro ⟨c, hConst⟩
    have hRegφ : IsRegularPoint ⟨univ, isOpen_univ⟩ φ ⟨0, mem_univ 0⟩ := by
      apply (isRegularPoint_iff_exists_open_neighborhood ⟨univ, isOpen_univ⟩ φ ⟨0, mem_univ 0⟩).mpr
      refine ⟨⟨univ, isOpen_univ⟩, mem_univ 0, subset_univ _, (fun _ => c), contDiff_const.contDiffOn, ?_⟩
      simpa only [Measure.restrict_univ] using hConst.symm
    exact hSource.mpr (hDensity.symm.trans (hLimit.mp hRegφ))

/-- Every actual tangent at an original singular point is nonconstant as an
almost-everywhere map class. -/
theorem IsTangentAt.not_ae_constant_of_singular {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hT : IsTangentAt u Du a.val φ Dφ) (hSing : a ∈ singularSet Ω u) :
    ¬ ∃ c : Ambient q, φ =ᵐ[volume] (fun _ => c) := by
  intro hConst
  exact hSing ((IsTangentAt.regular_iff_ae_constant hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT).mpr hConst)

/-- A constant actual tangent exists exactly at the original regular points. -/
theorem exists_ae_constant_tangent_iff_isRegularPoint {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) (a : Ω.val) :
    (∃ (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      IsTangentAt u Du a.val φ Dφ ∧ ∃ c : Ambient q, φ =ᵐ[volume] (fun _ => c)) ↔
      IsRegularPoint Ω u a := by
  constructor
  · rintro ⟨φ, Dφ, hT, hConst⟩
    exact (IsTangentAt.regular_iff_ae_constant hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT).mpr hConst
  · intro hReg
    let ρ : ℕ → PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
    have hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨_κ, φ, Dφ, _hκ, _hW, _hN, _hMin, _hStrong, _hEnergy, _hHom, hT⟩ :=
      exists_tangent_along_prescribed_scales hn N Ω u Du hu hTarget hMinimizer a ρ hρ
    exact ⟨φ, Dφ, hT,
      (IsTangentAt.regular_iff_ae_constant hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT).mp hReg⟩

/-- Every actual tangent at an original singular point has its same
characterized spine inside its singular set and of codimension at least three. -/
theorem IsTangentAt.spine_singular_and_finrank_le_of_singular {n q : ℕ} (hn : 3 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hT : IsTangentAt u Du a.val φ Dφ) (hSing : a ∈ singularSet Ω u) :
    let hn₂ : 2 ≤ n := Nat.le_of_succ_le hn
    let Q := IsTangentAt.qualification hn₂ N Ω u Du hu hTarget hMinimizer a φ Dφ hT
    ((spine hn₂ Q.2.2.1 Q.1 Q.2.1 Q.2.2.2.2 : Set (Domain n)) ⊆
      Subtype.val '' singularSet ⟨univ, isOpen_univ⟩ φ) ∧
      Module.finrank ℝ (spine hn₂ Q.2.2.1 Q.1 Q.2.1 Q.2.2.2.2) ≤ n - 3 := by
  intro hn₂ Q
  exact spine_singular_and_finrank_le hn Q.2.2.1 Q.1 Q.2.1 Q.2.2.2.2
    (IsTangentAt.not_ae_constant_of_singular hn₂ N Ω u Du hu hTarget hMinimizer a φ Dφ hT hSing)

end StratificationTheory
