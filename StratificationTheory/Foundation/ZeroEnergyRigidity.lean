module

public import HarmonicMaps.Analysis.SobolevPoincare
public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.SobolevRestriction
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Zero-energy rigidity

The actual Dirichlet energy and the ball Poincare inequality identify a
zero-energy Sobolev map with its ball average almost everywhere. Nested balls
give one constant on the whole Euclidean domain.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal

namespace StratificationTheory

theorem ae_eq_ball_average_of_dirichletEnergy_zero {n q : ℕ}
    {a : Domain n} {r : ℝ} (hr : 0 < r)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du)
    (hzero : dirichletEnergy Du (Metric.ball a r) = 0) :
    u =ᵐ[volume.restrict (Metric.ball a r)]
      (fun _ => ⨍ y in Metric.ball a r, u y) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huLp : MemLp u 2 (volume.restrict (Metric.ball a r)) := hu.2.1
  have henergyInt : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball a r) volume :=
    hu.integrable_hsNormSq
  have hE : (∫ x in Metric.ball a r, hsNormSq (Du x)) = 0 := by
    rw [← dirichletEnergy_toReal henergyInt, hzero, ENNReal.toReal_zero]
  have hp := hu.poincare_ball hr
  rw [hE, mul_zero] at hp
  have hI := (huLp.sub (memLp_const (⨍ y in Metric.ball a r, u y))).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have hnonneg : ∀ᵐ x ∂volume.restrict (Metric.ball a r),
      0 ≤ ‖u x - ⨍ y in Metric.ball a r, u y‖ ^ 2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hnull : (∫ x in Metric.ball a r, ‖u x - ⨍ y in Metric.ball a r, u y‖ ^ 2) = 0 :=
    le_antisymm hp (integral_nonneg fun _ => sq_nonneg _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnonneg hI).mp hnull] with x hx
  exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hx))

theorem exists_ae_eq_const_of_all_centered_energies_zero {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du) (a : Domain n)
    (hzero : ∀ r : PositiveRadius, dirichletEnergy Du (Metric.ball a r.val) = 0) :
    ∃ c : Ambient q, u =ᵐ[volume] (fun _ => c) := by
  let c : Ambient q := ⨍ y in Metric.ball a 1, u y
  have hunit : u =ᵐ[volume.restrict (Metric.ball a 1)] (fun _ => c) :=
    ae_eq_ball_average_of_dirichletEnergy_zero (by norm_num)
      (hu.memW12_ball (subset_univ _)) (hzero ⟨1, by norm_num⟩)
  have hball (k : ℕ) : u =ᵐ[volume.restrict (Metric.ball a ((k : ℝ) + 1))]
      (fun _ => c) := by
    have hr : 0 < (k : ℝ) + 1 := by positivity
    have havg := ae_eq_ball_average_of_dirichletEnergy_zero hr
      (hu.memW12_ball (subset_univ _)) (hzero ⟨_, hr⟩)
    have hsub : Metric.ball a 1 ⊆ Metric.ball a ((k : ℝ) + 1) :=
      Metric.ball_subset_ball (by linarith only [Nat.cast_nonneg (α := ℝ) k])
    have havgUnit : u =ᵐ[volume.restrict (Metric.ball a 1)]
        (fun _ => ⨍ y in Metric.ball a ((k : ℝ) + 1), u y) :=
      ae_restrict_of_ae_restrict_of_subset hsub havg
    have hconst := havgUnit.symm.trans hunit
    have hpoint := (volume : Measure (Domain n)).eqOn_open_of_ae_eq hconst
      Metric.isOpen_ball continuousOn_const continuousOn_const
    have heq : (⨍ y in Metric.ball a ((k : ℝ) + 1), u y) = c :=
      hpoint (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
    simpa only [heq] using havg
  refine ⟨c, ?_⟩
  have hwhole := (ae_eq_restrict_iUnion_iff
    (fun k : ℕ => Metric.ball a ((k : ℝ) + 1)) u (fun _ => c)).mpr hball
  simpa only [Metric.iUnion_ball_nat_succ, Measure.restrict_univ] using hwhole

theorem exists_ae_eq_target_const_of_all_centered_energies_zero {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (a : Domain n)
    (hzero : ∀ r : PositiveRadius, dirichletEnergy Du (Metric.ball a r.val) = 0) :
    ∃ c : Ambient q, c ∈ N.carrierSet ∧ u =ᵐ[volume] (fun _ => c) := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_all_centered_energies_zero hu a hzero
  have hcball : u =ᵐ[volume.restrict (Metric.ball a 1)] (fun _ => c) :=
    ae_restrict_of_ae hc
  have hNball : ∀ᵐ x ∂volume.restrict (Metric.ball a 1), u x ∈ N.carrierSet :=
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) hN
  obtain ⟨x, _hx, hxc, hxN⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos (volume : Measure (Domain n)) a (by norm_num : (0 : ℝ) < 1)).ne'
    (hcball.and hNball)
  have hcN : c ∈ N.carrierSet := by simpa only [hxc] using hxN
  exact ⟨c, hcN, hc⟩

end StratificationTheory
