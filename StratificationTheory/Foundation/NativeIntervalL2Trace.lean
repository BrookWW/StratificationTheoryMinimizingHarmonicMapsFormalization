module

public import StratificationTheory.Foundation.SurfaceL2TraceTransport
public import StratificationTheory.Foundation.CylinderCoordinateMeasure

/-!
# Native one-coordinate interval traces

The sole Euclidean coordinate preserves the restricted interval volume.
Every raw class of a continuous real-base L2 curve therefore transfers to
the literal native interval class, including its boundary parameter values.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The one-coordinate open cube is exactly the inverse real interval. -/
theorem native_one_cube_eq_interval (a b : ℝ) :
    (⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo a b) =
      {x : Domain 1 | x 0 ∈ Ioo a b} := by
  ext x
  simp only [mem_iInter, mem_preimage, mem_setOf_eq]
  constructor
  · intro h
    exact h 0
  · intro h j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h

/-- Actual interval volume, with no distortion factor, transports all raw
classes of a continuous L2 curve to the native one-coordinate cube. -/
theorem exists_native_interval_continuous_L2_curve
    {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E]
    (a b : ℝ) (H : C(T, Lp E 2 (volume.restrict (Ioo a b)))) :
    let S : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo a b
    ∃ K : C(T, Lp E 2 (volume.restrict S)),
      ∀ t (f : ℝ → E) (hf : MemLp f 2 (volume.restrict (Ioo a b))),
        H t = hf.toLp f →
        ∃ hs : MemLp (fun x : Domain 1 => f (x 0)) 2 (volume.restrict S),
          K t = hs.toLp (fun x : Domain 1 => f (x 0)) := by
  intro S
  let e : Domain 1 ≃ₜ ℝ :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph
  have hmap : Measure.map e (volume.restrict S) ≤
      (1 : ℝ≥0∞) • volume.restrict (Ioo a b) := by
    rw [one_smul]
    have hm := measurePreserving_domainOne_eval.restrict_preimage
      (measurableSet_Ioo (a := a) (b := b))
    have he : (e : Domain 1 → ℝ) = fun x => x 0 := rfl
    rw [he]
    change Measure.map (fun x : Domain 1 => x 0) (volume.restrict S) ≤ _
    rw [show S = (fun x : Domain 1 => x 0) ⁻¹' Ioo a b from
      native_one_cube_eq_interval a b]
    exact hm.map_eq.le
  obtain ⟨K, _hK, hraw, _hunique⟩ :=
    exists_continuous_L2_curve_homeomorph_pullback e (by norm_num) hmap H
  exact ⟨K, hraw⟩

end StratificationTheory
