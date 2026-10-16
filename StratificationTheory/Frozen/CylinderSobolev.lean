module

public import StratificationTheory.Frozen.UnitCylinder
public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Euclidean.Volume.Measure

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

/-- Source cylinder Sobolev membership uses native physical surface L2 and
one full finite radial weak extension on a spatial neighborhood times the
open time interval. Raw endpoint values are not prescribed by this predicate. -/
@[expose] def MemCylinderW12 {n q : ℕ} (_hn : 2 ≤ n) {a b : ℝ} (_hab : a < b)
    (v : unitCylinder n a b → Ambient q) : Prop :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  MemLp v 2 (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
    ∃ U : OpenDomain n, sphere (0 : Domain n) 1 ⊆ U.val ∧ (0 : Domain n) ∉ U.val ∧
      ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
        MemW12 ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage
              ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
                (continuous_snd.comp e.continuous)))⟩ w Dw ∧
        ∀ (ρ : PositiveRadius) (c : unitCylinder n a b),
          (e c.val).2 0 ∈ Ioo a b → ρ.val • (e c.val).1 ∈ U.val →
            w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = v c

end StratificationTheory
