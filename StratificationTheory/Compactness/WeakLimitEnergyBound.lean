module

public import StratificationTheory.Compactness.WeakEnergyLowerSemicontinuity
public import StratificationTheory.Compactness.WeakL2Localization
public import HarmonicMaps.SobolevRestriction

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- The same uniform finite ball-energy bound passes to an actual local
weak limit of the displayed gradient columns. -/
theorem dirichletEnergy_ball_weak_limit_le {n q : ℕ} {Ω : OpenDomain n}
    {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), LocallyMemL2 Ω (fun x => D k x i))
    (hDv : ∀ i : Fin n, LocallyMemL2 Ω (fun x => Dv x i))
    (hweak : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
        Tendsto (fun k => ∫ x in K, inner ℝ (D k x i) (w x)) atTop
          (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x))))
    {c : Domain n} {r : ℝ} (hclosed : closedBall c r ⊆ Ω.val)
    (C : ℝ≥0) (hEnergy : ∀ k, dirichletEnergy (D k) (ball c r) ≤ C) :
    dirichletEnergy Dv (ball c r) ≤ C := by
  have hDball (k : ℕ) (i : Fin n) : MemLp (fun x => D k x i) 2
      (volume.restrict (ball c r)) :=
    (hD k i (closedBall c r) (isCompact_closedBall c r) hclosed).mono_measure
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  have hDvball (i : Fin n) : MemLp (fun x => Dv x i) 2
      (volume.restrict (ball c r)) :=
    (hDv i (closedBall c r) (isCompact_closedBall c r) hclosed).mono_measure
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  have hweakball (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict (ball c r))) :
      Tendsto (fun k => ∫ x in ball c r, inner ℝ (D k x i) (w x)) atTop
        (𝓝 (∫ x in ball c r, inner ℝ (Dv x i) (w x))) :=
    weak_L2_integral_convergence_mono measurableSet_ball ball_subset_closedBall
      (hweak (closedBall c r) (isCompact_closedBall c r) hclosed i) w
  have hlower := dirichletEnergy_le_liminf_of_weak_columns hDball hDvball hweakball
  have hupper := liminf_le_liminf (f := atTop) (Eventually.of_forall hEnergy)
  simpa only [liminf_const] using hlower.trans hupper

end StratificationTheory.Compactness
