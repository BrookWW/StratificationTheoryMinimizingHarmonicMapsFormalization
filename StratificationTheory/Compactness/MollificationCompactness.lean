module

public import StratificationTheory.Compactness.MollificationFamilyBounds
public import StratificationTheory.Compactness.TotallyBoundedTransfer
public import HarmonicMaps.Analysis.VariableMollificationL2
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff NNReal ENNReal

namespace StratificationTheory.Compactness

/-- At every fixed scale, a uniformly L1-bounded family's actual mollifications
have compact closure in the uniform topology on every closed Euclidean ball. -/
theorem euclideanMollification_closedBall_compact_closure {ι : Type*} {n q : ℕ}
    (Ω : OpenDomain n) (u : ι → Domain n → Ambient q)
    (hu : ∀ i, IntegrableOn (u i) Ω.val volume)
    (C : ℝ≥0) (hbound : ∀ i, (∫ x in Ω.val, ‖u i x‖) ≤ C)
    (h : PositiveRadius) (a : Domain n) (r : ℝ) :
    letI : CompactSpace (Metric.closedBall a r) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall a r)
    IsCompact (closure (Set.range (fun i => BoundedContinuousFunction.mkOfCompact
      (⟨fun x : Metric.closedBall a r => euclideanMollification Ω (u i) (hu i) h x,
        (euclideanMollification_contDiff Ω (u i) (hu i) h).continuous.comp continuous_subtype_val⟩ :
        C(Metric.closedBall a r, Ambient q))))) := by
  letI : CompactSpace (Metric.closedBall a r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall a r)
  let M : ι → BoundedContinuousFunction (Metric.closedBall a r) (Ambient q) := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => euclideanMollification Ω (u i) (hu i) h x,
      (euclideanMollification_contDiff Ω (u i) (hu i) h).continuous.comp continuous_subtype_val⟩
  obtain ⟨B, L, hB, hL⟩ := euclideanMollification_family_uniform_bounds Ω u hu C hbound h
  let A := Set.range M
  have hALip (f : A) : LipschitzWith L (fun x => f.val x) := by
    obtain ⟨i, hi⟩ := f.property
    rw [← hi]
    simpa only [M, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      Function.comp_def, mul_one] using (hL i).comp (LipschitzWith.subtype_val (Metric.closedBall a r))
  have hEqui : Equicontinuous (fun f : A => fun x => f.val x) :=
    (LipschitzWith.uniformEquicontinuous _ L hALip).equicontinuous
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : Ambient q) (B : ℝ))
    (isCompact_closedBall _ _) A _ hEqui
  intro f x hf
  obtain ⟨i, rfl⟩ := hf
  simpa only [M, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
    Metric.mem_closedBall, dist_zero_right] using hB i x.val

/-- At a fixed scale, the actual mollifications of a uniformly L1-bounded
family form a totally bounded set in L2 on every Euclidean ball. -/
theorem euclideanMollification_ball_L2_totallyBounded {ι : Type*} {n q : ℕ}
    (Ω : OpenDomain n) (u : ι → Domain n → Ambient q)
    (hu : ∀ i, IntegrableOn (u i) Ω.val volume)
    (C : ℝ≥0) (hbound : ∀ i, (∫ x in Ω.val, ‖u i x‖) ≤ C)
    (h : PositiveRadius) (a : Domain n) (r : ℝ) :
    ∃ hm : ∀ i, MemLp (euclideanMollification Ω (u i) (hu i) h) 2
      (volume.restrict (Metric.ball a r)),
      TotallyBounded (range (fun i => (hm i).toLp (euclideanMollification Ω (u i) (hu i) h))) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : CompactSpace (Metric.closedBall a r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall a r)
  let M : ι → BoundedContinuousFunction (Metric.closedBall a r) (Ambient q) :=
    fun i => BoundedContinuousFunction.mkOfCompact
      ⟨fun x => euclideanMollification Ω (u i) (hu i) h x,
        (euclideanMollification_contDiff Ω (u i) (hu i) h).continuous.comp continuous_subtype_val⟩
  obtain ⟨B, _L, hB, _hL⟩ := euclideanMollification_family_uniform_bounds Ω u hu C hbound h
  have hm (i : ι) : MemLp (euclideanMollification Ω (u i) (hu i) h) 2
      (volume.restrict (Metric.ball a r)) :=
    MemLp.of_bound (euclideanMollification_contDiff Ω (u i) (hu i) h).continuous.aestronglyMeasurable
      (B : ℝ) (Filter.Eventually.of_forall fun x => hB i x)
  refine ⟨hm, ?_⟩
  have hcompact := euclideanMollification_closedBall_compact_closure Ω u hu C hbound h a r
  change IsCompact (closure (range M)) at hcompact
  have hTB : TotallyBounded (range M) := hcompact.totallyBounded.subset subset_closure
  apply totallyBounded_range_of_dist_control M _ hTB
    (Real.sqrt (volume.real (Metric.ball a r))) (Real.sqrt_nonneg _)
  intro i j
  let mi := euclideanMollification Ω (u i) (hu i) h
  let mj := euclideanMollification Ω (u j) (hu j) h
  have hsq : dist ((hm i).toLp mi) ((hm j).toLp mj) ^ 2 =
      ∫ x in Metric.ball a r, ‖mi x - mj x‖ ^ 2 := by
    rw [dist_eq_norm, ← (hm i).toLp_sub (hm j), Lp.norm_toLp,
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq ((hm i).sub (hm j))]
    rfl
  have hpoint {x : Domain n} (hx : x ∈ Metric.ball a r) :
      ‖mi x - mj x‖ ≤ dist (M i) (M j) := by
    have hp := BoundedContinuousFunction.dist_coe_le_dist (f := M i) (g := M j)
      (⟨x, Metric.ball_subset_closedBall hx⟩ : Metric.closedBall a r)
    simpa only [M, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      dist_eq_norm, mi, mj] using hp
  have hIntegral : (∫ x in Metric.ball a r, ‖mi x - mj x‖ ^ 2) ≤
      volume.real (Metric.ball a r) * dist (M i) (M j) ^ 2 := by
    have hle : (∫ x in Metric.ball a r, ‖mi x - mj x‖ ^ 2) ≤
        ∫ _x in Metric.ball a r, dist (M i) (M j) ^ 2 := by
      apply integral_mono_ae (((hm i).sub (hm j)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
        (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) (hpoint hx) 2
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] using hle
  have hFinal : dist ((hm i).toLp mi) ((hm j).toLp mj) ≤
      Real.sqrt (volume.real (Metric.ball a r)) * dist (M i) (M j) := by
    have hmass : 0 ≤ volume.real (Metric.ball a r) := ENNReal.toReal_nonneg
    have hRhs : Real.sqrt (volume.real (Metric.ball a r)) ^ 2 = volume.real (Metric.ball a r) :=
      Real.sq_sqrt hmass
    rw [← hsq] at hIntegral
    have hsquare : dist ((hm i).toLp mi) ((hm j).toLp mj) ^ 2 ≤
        (Real.sqrt (volume.real (Metric.ball a r)) * dist (M i) (M j)) ^ 2 := by
      rw [mul_pow, hRhs]
      exact hIntegral
    exact (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp hsquare
  exact hFinal

end StratificationTheory.Compactness
