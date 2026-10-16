module

public import StratificationTheory.Interpolation.RadialCutoffConstruction

/-!
# Smooth interior cutoffs near the unit sphere

Two radial cutoffs produce a single smooth scalar cutoff supported in a
closed collar and identically one on a smaller open collar. Its ordinary
coordinate derivatives vanish throughout that open collar.
-/

public section

open HarmonicMaps Metric Set Filter
open scoped ContDiff Topology

namespace StratificationTheory

/-- Every collar of width less than one half admits one smooth compact cutoff
equal to one, with zero coordinate derivatives, on the collar of half the width. -/
theorem exists_sphere_interior_cutoff {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∃ χ : Domain n → ℝ, ∃ hχ : ContDiff ℝ ∞ χ,
      HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} ∧
      (∀ x ∈ {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2}, χ x = 1) ∧
      ∀ x ∈ {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2},
        ∀ i : Fin n, coordinateDerivative χ hχ i x = 0 := by
  have hrinner : 0 < 1 - δ := by linarith only [hδsmall]
  have hrouter : 0 < 1 + δ / 2 := by linarith only [hδ]
  have hhalf : 0 < δ / 2 := half_pos hδ
  obtain ⟨χinner, hχinner, _, _, hinnerValues, hinnerOne, hinnerZero, _, _⟩ :=
    Interpolation.exists_quantitative_radial_cutoff (0 : Domain n) hrinner hhalf
  obtain ⟨χouter, hχouter, hcouter, _, houterValues, houterOne, houterZero, _, _⟩ :=
    Interpolation.exists_quantitative_radial_cutoff (0 : Domain n) hrouter hhalf
  let χ : Domain n → ℝ := fun x => (1 - χinner x) * χouter x
  have hχ : ContDiff ℝ ∞ χ := (contDiff_const.sub hχinner).mul hχouter
  have hcχ : HasCompactSupport χ := hcouter.mul_left
  have hvalues (x : Domain n) : 0 ≤ χ x ∧ χ x ≤ 1 := by
    exact ⟨mul_nonneg (sub_nonneg.mpr (hinnerValues x).2) (houterValues x).1,
      mul_le_one₀ (sub_le_self 1 (hinnerValues x).1)
        (houterValues x).1 (houterValues x).2⟩
  have hsupport : tsupport χ ⊆
      {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} := by
    apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    intro x hx
    constructor
    · by_contra hlower
      have hin : x ∈ closedBall (0 : Domain n) (1 - δ) :=
        mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge hlower))
      have hzero : χ x = 0 := by
        simp only [χ, hinnerOne x hin, sub_self, zero_mul]
      exact hx hzero
    · by_contra hupper
      change ¬ ‖x‖ ≤ 1 + δ at hupper
      have hout : x ∉ ball (0 : Domain n) (1 + δ / 2 + δ / 2) := by
        rw [mem_ball_zero_iff]
        linarith only [hupper]
      have hzero : χ x = 0 := by
        simp only [χ, houterZero x hout, mul_zero]
      exact hx hzero
  have hon (x : Domain n)
      (hx : x ∈ {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2}) :
      χ x = 1 := by
    have hin : x ∉ ball (0 : Domain n) (1 - δ + δ / 2) := by
      rw [mem_ball_zero_iff]
      linarith only [hx.1]
    have hout : x ∈ closedBall (0 : Domain n) (1 + δ / 2) :=
      mem_closedBall_zero_iff.mpr hx.2.le
    simp only [χ, hinnerZero x hin, houterOne x hout, sub_zero, mul_one]
  refine ⟨χ, hχ, hcχ, hvalues, hsupport, hon, ?_⟩
  intro x hx i
  have hopen : IsOpen {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hlocal : χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hon y hy
  change fderiv ℝ χ x (EuclideanSpace.single i 1) = 0
  rw [hlocal.fderiv_eq]
  rw [fderiv_const_apply]
  rfl

/-- A closed collar contained in an open domain admits one smooth cutoff
supported in that domain and constant on the smaller open collar. -/
theorem exists_sphere_interior_cutoff_in_openDomain {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 2) (U : OpenDomain n)
    (hclosed : {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} ⊆ U.val) :
    ∃ χ : Domain n → ℝ, ∃ hχ : ContDiff ℝ ∞ χ,
      HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ {x : Domain n | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ} ∧
      tsupport χ ⊆ U.val ∧
      (∀ x ∈ {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2}, χ x = 1) ∧
      ∀ x ∈ {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2},
        ∀ i : Fin n, coordinateDerivative χ hχ i x = 0 := by
  obtain ⟨χ, hχ, hcχ, hvalues, hsupport, hon, hderiv⟩ :=
    exists_sphere_interior_cutoff (n := n) hδ hδsmall
  exact ⟨χ, hχ, hcχ, hvalues, hsupport, hsupport.trans hclosed, hon, hderiv⟩

end StratificationTheory
