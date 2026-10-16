module

public import StratificationTheory.Compactness.UniformMollificationError
public import StratificationTheory.Compactness.MollificationCompactness
public import StratificationTheory.Compactness.TotallyBoundedApproximation

/-!
# Interior Rellich compactness

Uniform map L2 and actual Hilbert--Schmidt energy bounds on an outer ball give
strong map L2 subsequences on every strictly smaller concentric ball. The proof
uses the literal imported mollification, its proved uniform approximation error,
and compactness of each fixed-scale family.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

namespace StratificationTheory.Compactness

/-- Uniformly bounded map L2 norms and original HS energies of genuine W1,2
maps on an outer ball imply total boundedness of their map classes in L2 on
every strictly smaller concentric ball. -/
theorem memW12_ball_L2_totallyBounded {ι : Type*} {n q : ℕ}
    (a : Domain n) {r R : ℝ} (hR : 0 < R) (hrR : r < R)
    (u : ι → Domain n → Ambient q) (Du : ι → Domain n → Gradient n q)
    (hu : ∀ i, MemW12 (ballDomain a R) (u i) (Du i))
    (Cmap Cenergy : ℝ≥0)
    (hMap : ∀ i, (∫ x in Metric.ball a R, ‖u i x‖ ^ 2) ≤ Cmap)
    (hEnergy : ∀ i, dirichletEnergy (Du i) (Metric.ball a R) ≤ Cenergy) :
    ∃ hi : ∀ i, MemLp (u i) 2 (volume.restrict (Metric.ball a r)),
      TotallyBounded (range (fun i => (hi i).toLp (u i))) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hOuter (i : ι) : MemLp (u i) 2 (volume.restrict (Metric.ball a R)) := (hu i).2.1
  have hi (i : ι) : MemLp (u i) 2 (volume.restrict (Metric.ball a r)) :=
    (hu i).2.1.mono_measure (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le))
  let C : ℝ≥0 := ⟨volume.real (Metric.ball a R) + Cmap,
    add_nonneg ENNReal.toReal_nonneg Cmap.property⟩
  have hL1 (i : ι) : (∫ x in Metric.ball a R, ‖u i x‖) ≤ C := by
    have hNorm := ((hOuter i).integrable (by norm_num)).norm
    have hSq := (hOuter i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    have hle : (∫ x in Metric.ball a R, ‖u i x‖) ≤
        ∫ x in Metric.ball a R, (1 + ‖u i x‖ ^ 2) :=
      integral_mono hNorm ((integrable_const 1).add hSq)
        (fun x => by nlinarith [sq_nonneg (‖u i x‖ - 1)])
    rw [integral_add (integrable_const 1) hSq, integral_const] at hle
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one] at hle
    exact hle.trans (add_le_add (le_refl _) (hMap i))
  refine ⟨hi, ?_⟩
  apply totallyBounded_range_of_uniform_approximations
  intro ε hε
  let h : PositiveRadius := ⟨min (R - r) (ε / (Real.sqrt Cenergy + 1)),
    lt_min (sub_pos.mpr hrR) (div_pos hε (by positivity))⟩
  have hsmall : h.val ≤ ε / (Real.sqrt Cenergy + 1) := min_le_right _ _
  have hgap : h.val ≤ R - r := min_le_left _ _
  have hmargin : r + h.val / 2 < R := by nlinarith [h.property]
  obtain ⟨hm, hTB⟩ := euclideanMollification_ball_L2_totallyBounded (ballDomain a R) u
    (fun i => (hu i).integrable_ball) C hL1 h a r
  refine ⟨(fun i => (hm i).toLp (euclideanMollification (ballDomain a R) (u i) (hu i).integrable_ball h)),
    hTB, ?_⟩
  intro i
  let m := euclideanMollification (ballDomain a R) (u i) (hu i).integrable_ball h
  have hdistSq : dist ((hi i).toLp (u i)) ((hm i).toLp m) ^ 2 =
      ∫ x in Metric.ball a r, ‖m x - u i x‖ ^ 2 := by
    rw [dist_comm, dist_eq_norm, ← (hm i).toLp_sub (hi i), Lp.norm_toLp,
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq ((hm i).sub (hi i))]
    rfl
  have hEnergyReal : (∫ x in Metric.ball a R, hsNormSq (Du i x)) ≤ Cenergy := by
    have hE := ENNReal.toReal_mono (by simp : (Cenergy : ℝ≥0∞) ≠ ⊤) (hEnergy i)
    have hInt : IntegrableOn (fun x => hsNormSq (Du i x)) (Metric.ball a R) volume :=
      (hu i).integrable_hsNormSq
    rw [dirichletEnergy_toReal hInt, ENNReal.coe_toReal] at hE
    exact hE
  have hSq : dist ((hi i).toLp (u i)) ((hm i).toLp m) ^ 2 ≤
      (h.val ^ 2 / 4) * Cenergy := by
    rw [hdistSq]
    exact (memW12_mollification_L2_square_error_le a hR h hmargin (hu i)).trans
      (mul_le_mul_of_nonneg_left hEnergyReal (by positivity))
  have hSq' : dist ((hi i).toLp (u i)) ((hm i).toLp m) ^ 2 ≤
      (h.val / 2 * Real.sqrt Cenergy) ^ 2 := by
    have heq : (h.val / 2 * Real.sqrt Cenergy) ^ 2 = (h.val ^ 2 / 4) * Cenergy := by
      rw [mul_pow, Real.sq_sqrt (show 0 ≤ (Cenergy : ℝ) from Cenergy.property)]
      ring
    rwa [heq]
  have hdist : dist ((hi i).toLp (u i)) ((hm i).toLp m) ≤ h.val / 2 * Real.sqrt Cenergy :=
    (sq_le_sq₀ dist_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp hSq'
  have hsmallMul : h.val * (Real.sqrt Cenergy + 1) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp hsmall
  have hhalf : h.val / 2 ≤ h.val := by linarith [h.property]
  have hle := mul_le_mul_of_nonneg_right hhalf (Real.sqrt_nonneg (Cenergy : ℝ))
  have hrest : h.val * Real.sqrt Cenergy ≤ h.val * (Real.sqrt Cenergy + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) h.property.le
  exact hdist.trans (hle.trans (hrest.trans hsmallMul))

/-- Interior Rellich extraction for genuine explicit-gradient Sobolev maps:
one strictly increasing subsequence converges strongly in L2 on the fixed
smaller ball to one actual ambient function. -/
theorem memW12_exists_strong_L2_subsequence_ball {n q : ℕ}
    (a : Domain n) {r R : ℝ} (hR : 0 < R) (hrR : r < R)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12 (ballDomain a R) (u k) (Du k))
    (Cmap Cenergy : ℝ≥0)
    (hMap : ∀ k, (∫ x in Metric.ball a R, ‖u k x‖ ^ 2) ≤ Cmap)
    (hEnergy : ∀ k, dirichletEnergy (Du k) (Metric.ball a R) ≤ Cenergy) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q),
      StrictMono κ ∧ MemLp v 2 (volume.restrict (Metric.ball a r)) ∧
      Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict (Metric.ball a r)))
        atTop (𝓝 0) := by
  obtain ⟨hi, hTB⟩ := memW12_ball_L2_totallyBounded a hR hrR u Du hu Cmap Cenergy hMap hEnergy
  have hcompact := hTB.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨v, _hv, κ, hκ, hconv⟩ := hcompact.tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  have hv : MemLp (v : Domain n → Ambient q) 2 (volume.restrict (Metric.ball a r)) := Lp.memLp v
  refine ⟨κ, (v : Domain n → Ambient q), hκ, hv, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => u (κ k)) (fun k => hi (κ k))
    (v : Domain n → Ambient q) hv).mp
  rw [Lp.toLp_coeFn]
  exact hconv

end StratificationTheory.Compactness
