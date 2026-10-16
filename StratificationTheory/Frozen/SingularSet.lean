module

public import StratificationTheory.Frozen.RegularPoint

@[expose] public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StratificationTheory

def singularSet {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) : Set Ω.val :=
  {a | ¬ IsRegularPoint Ω u a}


end StratificationTheory
