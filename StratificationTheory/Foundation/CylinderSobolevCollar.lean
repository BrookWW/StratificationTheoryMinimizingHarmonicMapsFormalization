module

public import StratificationTheory.Frozen.CylinderSobolev
public import StratificationTheory.Foundation.SphereNeighborhoodCollar

/-!
# Uniform spatial collars for cylinder Sobolev data

The complete literal cylinder Sobolev predicate is equivalent to the same
finite weak extension on a uniform radial collar. The original map, all weak
columns, the whole open time interval and every admitted raw ray are retained.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

/-- A uniform spatial collar suffices for full finite cylinder Sobolev
membership, with the same native surface class and all time directions. -/
theorem memCylinderW12_iff_exists_radial_collar {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q) :
    MemCylinderW12 hn hab v ↔
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      MemLp v 2 (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
        ∃ U : OpenDomain n,
          U.val = {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} ∧
          sphere (0 : Domain n) 1 ⊆ U.val ∧ (0 : Domain n) ∉ U.val ∧
          ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
            MemW12 ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
              (U.property.preimage (continuous_fst.comp e.continuous)).inter
                (isOpen_Ioo.preimage
                  ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
                    (continuous_snd.comp e.continuous)))⟩ w Dw ∧
            ∀ (ρ : PositiveRadius) (c : unitCylinder n a b),
              (e c.val).2 0 ∈ Ioo a b → ρ.val • (e c.val).1 ∈ U.val →
                w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = v c := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  constructor
  · rintro ⟨hLp, U, hSphere, _hzero, w, Dw, hW, hraw⟩
    obtain ⟨δ, hδ, hδsmall, hsub⟩ := exists_radial_collar_subset U hSphere
    let V : OpenDomain n := ⟨{x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ},
      isOpen_radial_collar δ⟩
    have hVsub : V.val ⊆ U.val := hsub
    refine ⟨hLp, δ, hδ, hδsmall, V, rfl,
      sphere_subset_radial_collar hδ,
      zero_not_mem_radial_collar (by linarith only [hδsmall]), w, Dw, ?_, ?_⟩
    · have hs : {y : Domain (n + 1) | (e y).1 ∈ V.val ∧ (e y).2 0 ∈ Ioo a b} ⊆
          {y : Domain (n + 1) | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b} :=
        fun _ hy => ⟨hVsub hy.1, hy.2⟩
      exact ⟨hW.1.mono hs,
        MemLp.mono_measure (Measure.restrict_mono_set volume hs) hW.2.1,
        fun i => MemLp.mono_measure (Measure.restrict_mono_set volume hs) (hW.2.2 i)⟩
    · intro ρ c ht hx
      exact hraw ρ c ht (hVsub hx)
  · rintro ⟨hLp, δ, _hδ, _hδsmall, U, _hU, hSphere, hzero, w, Dw, hW, hraw⟩
    exact ⟨hLp, U, hSphere, hzero, w, Dw, hW, hraw⟩

end StratificationTheory
