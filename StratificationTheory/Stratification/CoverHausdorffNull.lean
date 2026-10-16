/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Stratification.IteratedCover
public import Mathlib.MeasureTheory.Measure.Hausdorff

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Hausdorff nullity from contracting finite covers

Actual iterated finite covers have diameters tending to zero. Their total
diameter powers tend to zero when the cardinal multiplier times the radius
multiplier to that power is strictly below one. The native Hausdorff-cover
formula then gives local nullity. Actual finite internal covers give nullity
of bounded pieces. Countable centered-ball covers, or bounded exhaustion of
the Euclidean domain, give nullity of the whole set.
The finite one-step rule remains an explicit premise of these internal lemmas.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace StratificationTheory

/-- A bounded set in a proper metric space has an actual finite open-ball
cover at any positive radius, with every center belonging to that set. -/
theorem exists_finset_internal_cover_of_bounded {X : Type*} [MetricSpace X] [ProperSpace X]
    (B : Set X) (hB : Bornology.IsBounded B) (R : ℝ) (hR : 0 < R) :
    ∃ C : Finset X, (∀ c ∈ C, c ∈ B) ∧
      ∀ x ∈ B, ∃ c ∈ C, dist x c < R := by
  classical
  let ε : ℝ≥0 := NNReal.mk (R / 2) (half_pos hR).le
  have hε : ε ≠ 0 := by
    intro hzero
    have hhalf : R / 2 = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) hzero
    exact (half_pos hR).ne' hhalf
  obtain ⟨N, hNB, hNfinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact_closure hε hB.isCompact_closure
  refine ⟨hNfinite.toFinset, fun c hc => hNB (hNfinite.mem_toFinset.mp hc), ?_⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hcover hx
  have hdist : dist x c ≤ R / 2 := by
    change edist x c ≤ (ε : ℝ≥0∞) at hxc
    simpa only [edist_dist, ENNReal.ofReal_le_coe, ε, NNReal.coe_mk] using hxc
  exact ⟨c, hNfinite.mem_toFinset.mpr hc, hdist.trans_lt (half_lt_self hR)⟩

/-- A contracting finite covering rule gives native Hausdorff nullity on
each admissible ball, from the actual finite covers at every generation. -/
theorem hausdorffMeasure_zero_local_of_contracting_finset_cover {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (σ r₀ : ℝ) (K : ℕ) (hσ : 0 < σ) (hσone : σ < 1)
    (hstep : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset X, (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < σ * r) ∧ C.card ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hcontract : (K : ℝ) * σ ^ d < 1)
    (a : X) (ha : a ∈ A) (R : ℝ) (hR : 0 < R) (hRr₀ : R ≤ r₀) :
    μH[d] (A ∩ ball a R) = 0 := by
  classical
  choose C _hCA hcover hcard using
    exists_iterated_finset_cover A σ r₀ K hσ hσone hstep a ha R hR hRr₀
  have hdiams (k : ℕ) (c : C k) :
      ediam (ball c.val (σ ^ k * R)) ≤ ENNReal.ofReal (2 * (σ ^ k * R)) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' : dist c.val y < σ ^ k * R := by
      rw [dist_comm]
      exact mem_ball.mp hy
    calc
      dist x y ≤ dist x c.val + dist c.val y := dist_triangle _ _ _
      _ ≤ 2 * (σ ^ k * R) := by linarith only [hx', hy']
  have hsetcover (k : ℕ) : A ∩ ball a R ⊆ ⋃ c : C k, ball c.val (σ ^ k * R) := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hcover k x hx
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, mem_ball.mpr hxc⟩
  have hsum (k : ℕ) :
      (∑ c : C k, ediam (ball c.val (σ ^ k * R)) ^ d) ≤
        ENNReal.ofReal ((2 * R) ^ d * ((K : ℝ) * σ ^ d) ^ k) := by
    have hcardENN : ((C k).card : ℝ≥0∞) ≤ (K : ℝ≥0∞) ^ k := by
      exact_mod_cast hcard k
    have hNatENN : ENNReal.ofReal ((K : ℝ) ^ k) = (K : ℝ≥0∞) ^ k := by
      rw [← Nat.cast_pow, ENNReal.ofReal_natCast, Nat.cast_pow]
    have hpowReal : (2 * (σ ^ k * R)) ^ d = (2 * R) ^ d * (σ ^ d) ^ k := by
      rw [show 2 * (σ ^ k * R) = (2 * R) * σ ^ k from by ring,
        Real.mul_rpow (by positivity) (pow_nonneg hσ.le k),
        ← Real.rpow_pow_comm hσ.le d k]
    calc
      (∑ c : C k, ediam (ball c.val (σ ^ k * R)) ^ d) ≤
          ∑ _c : C k, (ENNReal.ofReal (2 * (σ ^ k * R))) ^ d :=
        Finset.sum_le_sum (fun c _ => ENNReal.rpow_le_rpow (hdiams k c) hd)
      _ = ((C k).card : ℝ≥0∞) * (ENNReal.ofReal (2 * (σ ^ k * R))) ^ d := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ (K : ℝ≥0∞) ^ k * (ENNReal.ofReal (2 * (σ ^ k * R))) ^ d :=
        mul_le_mul_of_nonneg_right hcardENN zero_le
      _ = ENNReal.ofReal ((2 * R) ^ d * ((K : ℝ) * σ ^ d) ^ k) := by
        rw [← hNatENN,
          ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2 * (σ ^ k * R)) hd,
          ← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg K) k)]
        congr 1
        rw [hpowReal, mul_pow]
        ring
  have hscale : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * (σ ^ k * R)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [zero_mul, mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hσ.le hσone).mul_const R).const_mul 2)
  have hfactor : 0 ≤ (K : ℝ) * σ ^ d :=
    mul_nonneg (Nat.cast_nonneg K) (Real.rpow_nonneg hσ.le d)
  have htotal : Tendsto
      (fun k : ℕ => ENNReal.ofReal ((2 * R) ^ d * ((K : ℝ) * σ ^ d) ^ k))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hfactor hcontract).const_mul ((2 * R) ^ d))
  have hsumlimit : Tendsto
      (fun k : ℕ => ∑ c : C k, ediam (ball c.val (σ ^ k * R)) ^ d)
      atTop (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htotal
      (fun _ => zero_le) hsum
  have hH := Measure.hausdorffMeasure_le_liminf_sum d (A ∩ ball a R)
    (fun k : ℕ => ENNReal.ofReal (2 * (σ ^ k * R))) hscale
    (fun k (c : C k) => ball c.val (σ ^ k * R))
    (Eventually.of_forall hdiams) (Eventually.of_forall hsetcover)
  rw [hsumlimit.liminf_eq] at hH
  exact le_antisymm hH zero_le

/-- Countably many actual balls centered in the set globalize the local
Hausdorff nullity of a contracting finite covering rule. -/
theorem hausdorffMeasure_zero_of_contracting_finset_cover {X : Type*}
    [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (σ r₀ : ℝ) (K : ℕ) (hσ : 0 < σ) (hσone : σ < 1) (hr₀ : 0 < r₀)
    (hstep : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset X, (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < σ * r) ∧ C.card ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hcontract : (K : ℝ) * σ ^ d < 1) :
    μH[d] A = 0 := by
  have hcover : A ⊆ ⋃ p : A, ball p.val r₀ := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hr₀⟩
  obtain ⟨T, hcount, hT⟩ := isOpen_iUnion_countable (fun p : A => ball p.val r₀)
    (fun _ => isOpen_ball)
  have hTcover : A ⊆ ⋃ p ∈ T, A ∩ ball p.val r₀ := by
    intro x hx
    have hxb : x ∈ ⋃ p ∈ T, ball p.val r₀ := by rw [hT]; exact hcover hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hxb
    obtain ⟨hpT, hxp⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpT, hx, hxp⟩⟩
  apply measure_mono_null hTcover
  apply (measure_biUnion_null_iff hcount).mpr
  intro p _hp
  exact hausdorffMeasure_zero_local_of_contracting_finset_cover A σ r₀ K hσ hσone hstep
    d hd hcontract p.val p.property r₀ hr₀ le_rfl

/-- The actual initial finite cover of a bounded subset has centers in the
original set, so the local nullity theorem applies to each of its balls. -/
theorem hausdorffMeasure_zero_bounded_piece_of_contracting_finset_cover {X : Type*}
    [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    (A B : Set X) (hBA : B ⊆ A) (hB : Bornology.IsBounded B)
    (σ r₀ : ℝ) (K : ℕ) (hσ : 0 < σ) (hσone : σ < 1) (hr₀ : 0 < r₀)
    (hstep : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset X, (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < σ * r) ∧ C.card ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hcontract : (K : ℝ) * σ ^ d < 1) :
    μH[d] B = 0 := by
  obtain ⟨C, hCB, hcover⟩ := exists_finset_internal_cover_of_bounded B hB r₀ hr₀
  have hBcover : B ⊆ ⋃ c ∈ C, A ∩ ball c r₀ := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hc, hBA hx, mem_ball.mpr hxc⟩⟩
  apply measure_mono_null hBcover
  apply (measure_biUnion_null_iff C.finite_toSet.countable).mpr
  intro c hc
  exact hausdorffMeasure_zero_local_of_contracting_finset_cover A σ r₀ K hσ hσone hstep
    d hd hcontract c (hBA (hCB c hc)) r₀ hr₀ le_rfl

/-- Native Euclidean Hausdorff nullity globalizes from actual finite covers
of the bounded pieces `A ∩ closedBall 0 k`. The zero-dimensional ambient
space is included. -/
theorem hausdorffMeasure_zero_of_contracting_finset_cover_bounded_exhaustion {n : ℕ}
    (A : Set (Domain n)) (σ r₀ : ℝ) (K : ℕ)
    (hσ : 0 < σ) (hσone : σ < 1) (hr₀ : 0 < r₀)
    (hstep : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset (Domain n), (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < σ * r) ∧ C.card ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hcontract : (K : ℝ) * σ ^ d < 1) :
    μH[d] A = 0 := by
  let B : ℕ → Set (Domain n) := fun k => A ∩ closedBall (0 : Domain n) (k : ℝ)
  have hBnull (k : ℕ) : μH[d] (B k) = 0 :=
    hausdorffMeasure_zero_bounded_piece_of_contracting_finset_cover A (B k)
      inter_subset_left (isBounded_closedBall.subset inter_subset_right)
      σ r₀ K hσ hσone hr₀ hstep d hd hcontract
  have hcover : A ⊆ ⋃ k : ℕ, B k := by
    intro x hx
    refine mem_iUnion.mpr ⟨Nat.ceil ‖x‖, hx, ?_⟩
    exact (show dist x (0 : Domain n) ≤ (Nat.ceil ‖x‖ : ℝ) from by
      simpa only [dist_zero_right] using Nat.le_ceil ‖x‖)
  exact measure_mono_null hcover (measure_iUnion_null hBnull)

end StratificationTheory
