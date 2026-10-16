module

public import StratificationTheory.TangentMaps.TangentQualification
public import StratificationTheory.Frozen.SpineCharacterization
public import StratificationTheory.Frozen.SingularSet

public section
open HarmonicMaps MeasureTheory Metric Set Module

namespace StratificationTheory

/-- Singular points whose every actual strong tangent has characterized
spine dimension at most the given index. Tangent qualifications are derived
for each raw tangent, rather than used to restrict the quantified family. -/
@[expose] def singularStratum {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) (j : ℕ) : Set Ω.val :=
  {a | a ∈ singularSet Ω u ∧
    ∀ (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
      (hT : IsTangentAt u Du a.val φ Dφ),
      let Q := IsTangentAt.qualification hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT
      finrank ℝ (spine hn Q.2.2.1 Q.1 Q.2.1 Q.2.2.2.2) ≤ j}

end StratificationTheory
