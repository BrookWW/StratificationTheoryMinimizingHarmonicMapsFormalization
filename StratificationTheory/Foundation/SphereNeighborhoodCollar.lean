module
public import HarmonicMaps.SobolevRestriction
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith

/-!
# Uniform radial collars around the unit sphere

Every open Euclidean neighborhood of the unit sphere contains a uniform radial
collar. A smaller closed collar is compact and avoids the origin. Local Sobolev
data on the neighborhood restrict to finite Sobolev data on the open collar.
-/

public section

open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

private theorem dist_normalize_eq {n : ℕ} {x : Domain n} (hx : x ≠ 0) :
    dist x (‖x‖⁻¹ • x) = |‖x‖ - 1| := by
  have hnorm : ‖NormedSpace.normalize x‖ = 1 := NormedSpace.norm_normalize hx
  change dist x (NormedSpace.normalize x) = _
  calc
    dist x (NormedSpace.normalize x) =
        ‖‖x‖ • NormedSpace.normalize x - (1 : ℝ) • NormedSpace.normalize x‖ := by
      rw [NormedSpace.norm_smul_normalize, one_smul, dist_eq_norm]
    _ = |‖x‖ - 1| := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, hnorm, mul_one]

/-- Every open neighborhood of the unit sphere contains one uniform radial collar. -/
theorem exists_radial_collar_subset {n : ℕ} (U : OpenDomain n)
    (hSphere : sphere (0 : Domain n) 1 ⊆ U.val) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} ⊆ U.val := by
  obtain ⟨ε, hε, hthick⟩ :=
    (isCompact_sphere (0 : Domain n) 1).exists_thickening_subset_open U.property hSphere
  let δ : ℝ := min ε (1 / 4)
  have hδpos : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδsmall : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨δ, hδpos, hδsmall, ?_⟩
  intro x hx
  have hxpos : 0 < ‖x‖ := by linarith [hx.1]
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  apply hthick
  apply mem_thickening_iff.mpr
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize hx0
  · rw [dist_normalize_eq hx0]
    apply lt_of_lt_of_le _ hδε
    exact abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The radial collar is open in the actual Euclidean domain. -/
theorem isOpen_radial_collar {n : ℕ} (δ : ℝ) :
    IsOpen {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} := by
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

/-- The unit sphere lies in every radial collar of positive width. -/
theorem sphere_subset_radial_collar {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    sphere (0 : Domain n) 1 ⊆
      {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} := by
  intro x hx
  have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  rw [Set.mem_setOf_eq, hnorm]
  constructor <;> linarith

/-- A radial collar of width at most one avoids the origin. -/
theorem zero_not_mem_radial_collar {n : ℕ} {δ : ℝ} (hδ : δ ≤ 1) :
    (0 : Domain n) ∉ {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} := by
  intro hx
  have hlo := hx.1
  rw [norm_zero] at hlo
  linarith

/-- A closed radial collar is compact, including in dimension zero. -/
theorem isCompact_closed_radial_collar {n : ℕ} (δ : ℝ) :
    IsCompact {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} := by
  apply (isCompact_closedBall (0 : Domain n) (1 + δ)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    exact mem_closedBall_zero_iff.mpr hx.2

/-- A closed radial collar of width less than one avoids the origin. -/
theorem zero_not_mem_closed_radial_collar {n : ℕ} {δ : ℝ} (hδ : δ < 1) :
    (0 : Domain n) ∉ {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} := by
  intro hx
  have hlo := hx.1
  rw [norm_zero] at hlo
  linarith

/-- Every open neighborhood of the unit sphere contains a closed radial collar. -/
theorem exists_closed_radial_collar_subset {n : ℕ} (U : OpenDomain n)
    (hSphere : sphere (0 : Domain n) 1 ⊆ U.val) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} ⊆ U.val := by
  obtain ⟨ε, hε, hεsmall, hcollar⟩ := exists_radial_collar_subset U hSphere
  refine ⟨ε / 2, by linarith, by linarith, ?_⟩
  intro x hx
  apply hcollar
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Local Sobolev membership restricts to finite membership on a collar
whose closed collar lies in the original domain. -/
theorem memW12_radial_collar {n q : ℕ} {U : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc U u Du) {δ : ℝ}
    (hclosed : {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} ⊆ U.val) :
    MemW12 ⟨{x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ},
      isOpen_radial_collar δ⟩ u Du := by
  have hsub : {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} ⊆
      {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} :=
    fun _ hx => ⟨hx.1.le, hx.2.le⟩
  refine ⟨hu.1.mono (hsub.trans hclosed), ?_, ?_⟩
  · exact MemLp.mono_measure (Measure.restrict_mono_set volume hsub)
      (hu.2.1 _ (isCompact_closed_radial_collar δ) hclosed)
  · intro i
    exact MemLp.mono_measure (Measure.restrict_mono_set volume hsub)
      (hu.2.2 i _ (isCompact_closed_radial_collar δ) hclosed)

/-- Local Sobolev data near the unit sphere have finite Sobolev data on one
uniform radial collar whose compact closed collar lies in that neighborhood. -/
theorem exists_memW12_radial_collar {n q : ℕ} {U : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hSphere : sphere (0 : Domain n) 1 ⊆ U.val) (hu : MemW12Loc U u Du) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} ⊆ U.val ∧
      MemW12 ⟨{x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ},
        isOpen_radial_collar δ⟩ u Du := by
  obtain ⟨δ, hδ, hδsmall, hclosed⟩ := exists_closed_radial_collar_subset U hSphere
  exact ⟨δ, hδ, hδsmall, hclosed, memW12_radial_collar hu hclosed⟩

end StratificationTheory
