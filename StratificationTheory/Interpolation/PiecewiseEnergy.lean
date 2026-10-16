module

public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

public section

open HarmonicMaps MeasureTheory Set
open scoped Classical

namespace StratificationTheory.Interpolation

/-- The actual HS energy of a ball-piecewise gradient splits into the inner
energy and the unchanged outer region, including possibly infinite energies. -/
theorem dirichletEnergy_piecewise_ball {n q : ℕ} {a : Domain n} {r R : ℝ}
    (hrR : r ≤ R) (Du Dv : Domain n → Gradient n q) :
    dirichletEnergy ((Metric.ball a r).piecewise Dv Du) (Metric.ball a R) =
      dirichletEnergy Dv (Metric.ball a r) +
        dirichletEnergy Du (Metric.ball a R \ Metric.ball a r) := by
  have heq : (fun x => ENNReal.ofReal (hsNormSq ((Metric.ball a r).piecewise Dv Du x))) =
      (Metric.ball a r).piecewise (fun x => ENNReal.ofReal (hsNormSq (Dv x)))
        (fun x => ENNReal.ofReal (hsNormSq (Du x))) := by
    funext x
    by_cases hx : x ∈ Metric.ball a r
    · simp only [piecewise_eq_of_mem _ _ _ hx]
    · simp only [piecewise_eq_of_notMem _ _ _ hx]
  have hset : (Metric.ball a r)ᶜ ∩ Metric.ball a R = Metric.ball a R \ Metric.ball a r := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    exact and_comm
  unfold dirichletEnergy
  rw [heq, lintegral_piecewise measurableSet_ball,
    Measure.restrict_restrict measurableSet_ball,
    Measure.restrict_restrict measurableSet_ball.compl,
    inter_eq_left.mpr (Metric.ball_subset_ball hrR), hset]

end StratificationTheory.Interpolation
