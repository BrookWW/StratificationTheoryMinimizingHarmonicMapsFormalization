module

public import HolderToCK.Analysis.Bootstrap.AffineMinimizer
import Mathlib.Topology.MetricSpace.Basic

/-!
# Rescaled maps on expanding domains

Moving centers converging to an interior point and scales tending to zero
eventually send each fixed bounded ball into the original domain. The actual
Sobolev functions and gradients then inherit local minimality by the imported
arbitrary-ball transport theorem. These are domain and transport lemmas;
compactness and tangent-map extraction require additional proofs.
-/

public section

open HarmonicMaps Filter Set
open scoped Topology

namespace StratificationTheory

theorem eventually_closedBall_rescaling_subset {n : ℕ} {ι : Type*}
    {l : Filter ι} (Ω : OpenDomain n) {a : Domain n} (ha : a ∈ Ω.val)
    {centers : ι → Domain n} {scales : ι → ℝ}
    (hcenters : Tendsto centers l (𝓝 a)) (hscales : Tendsto scales l (𝓝 0))
    (L : ℝ) :
    ∀ᶠ k in l, ∀ z ∈ Metric.closedBall (0 : Domain n) L,
      centers k + scales k • z ∈ Ω.val := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp Ω.property a ha
  have hdist : Tendsto (fun k => dist (centers k) a) l (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hcenters
  have hbound : Tendsto (fun k => dist (centers k) a + ‖scales k‖ * |L|) l (𝓝 0) := by
    simpa only [norm_zero, zero_mul, zero_add] using hdist.add (hscales.norm.mul_const |L|)
  have hevent : ∀ᶠ k in l, dist (centers k) a + ‖scales k‖ * |L| < R :=
    hbound.eventually (gt_mem_nhds hR)
  filter_upwards [hevent] with k hk
  intro z hz
  apply hball
  rw [Metric.mem_ball]
  have hzL : ‖z‖ ≤ |L| := by
    have hz' : ‖z‖ ≤ L := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact hz'.trans (le_abs_self L)
  have hmove : dist (centers k + scales k • z) (centers k) ≤ ‖scales k‖ * |L| := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact mul_le_mul_of_nonneg_left hzL (norm_nonneg _)
  calc
    dist (centers k + scales k • z) a ≤
        dist (centers k + scales k • z) (centers k) + dist (centers k) a :=
      dist_triangle _ _ _
    _ ≤ ‖scales k‖ * |L| + dist (centers k) a := add_le_add hmove le_rfl
    _ < R := by simpa only [add_comm] using hk

theorem eventually_scaled_closedBall_subset {n : ℕ} {ι : Type*}
    {l : Filter ι} (Ω : OpenDomain n) {a : Domain n} (ha : a ∈ Ω.val)
    {centers : ι → Domain n} {scales : ι → PositiveRadius}
    (hcenters : Tendsto centers l (𝓝 a))
    (hscales : Tendsto (fun k => (scales k).val) l (𝓝 0))
    (L : PositiveRadius) :
    ∀ᶠ k in l, Metric.closedBall (centers k) ((scales k).val * L.val) ⊆ Ω.val := by
  have hevent := eventually_closedBall_rescaling_subset Ω ha hcenters hscales L.val
  filter_upwards [hevent] with k hk
  intro x hx
  let z : Domain n := (scales k).val⁻¹ • (x - centers k)
  have hmap : centers k + (scales k).val • z = x := by
    dsimp only [z]
    simp only [smul_smul, mul_inv_cancel₀ (scales k).property.ne', one_smul,
      add_sub_cancel]
  have hz : z ∈ Metric.closedBall (0 : Domain n) L.val := by
    have h := (HarmonicMaps.affineBall_mem_closedBall_iff (centers k) (0 : Domain n)
      (scales k).property ((scales k).val * L.val) z).mp (by
        simpa only [sub_zero, hmap] using hx)
    simpa only [mul_div_cancel_left₀ _ (scales k).property.ne'] using h
  rw [← hmap]
  exact hk z hz

theorem eventually_rescaled_minimizer_on_ball {n q : ℕ} {ι : Type*}
    {l : Filter ι} (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    {a : Domain n} (ha : a ∈ Ω.val)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du)
    {centers : ι → Domain n} {scales : ι → PositiveRadius}
    (hcenters : Tendsto centers l (𝓝 a))
    (hscales : Tendsto (fun k => (scales k).val) l (𝓝 0))
    (L : PositiveRadius) :
    ∀ᶠ k in l,
      let v : Domain n → Ambient q := fun z => u (centers k + (scales k).val • z)
      let Dv : Domain n → Gradient n q :=
        fun z i => (scales k).val • Du (centers k + (scales k).val • z) i
      MemW12 (ballDomain (0 : Domain n) L.val) v Dv ∧
      TakesValuesIn N (ballDomain (0 : Domain n) L.val) v ∧
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) v Dv := by
  have hevent := eventually_scaled_closedBall_subset Ω ha hcenters hscales L
  filter_upwards [hevent] with k hk
  let R : PositiveRadius :=
    ⟨(scales k).val * L.val, mul_pos (scales k).property L.property⟩
  have hratio : R.val / (scales k).val = L.val :=
    mul_div_cancel_left₀ L.val (scales k).property.ne'
  have htransport := HolderToCK.affineBall_minimizer_transport_on
    N Ω (centers k) R (scales k) u Du hk hu hN hmin
  have hfinite := (hu.memW12_ball hk).affineBall_pullback
    (0 : Domain n) (scales k).property
  simp only [sub_zero, mul_div_cancel_left₀ _ (scales k).property.ne'] at hfinite
  rw [hratio] at htransport
  exact ⟨hfinite, htransport.2.1, htransport.2.2⟩

end StratificationTheory
