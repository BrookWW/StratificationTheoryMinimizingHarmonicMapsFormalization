module

public import StratificationTheory.Foundation.CubicalFrameSeamWeakPair
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

public section

open HarmonicMaps Set Metric Filter
open scoped Topology

namespace StratificationTheory

/-- Every point whose continuous image lies in an open set has an actual
open neighborhood with compact closure and the same image inclusion. -/
theorem exists_compact_open_patch_preimage {a b : ℕ}
    {F : Domain a → Domain b} (hF : Continuous F) {O : Set (Domain b)}
    (hO : IsOpen O) {z : Domain a} (hz : F z ∈ O) :
    ∃ U : OpenDomain a, z ∈ U.val ∧ IsCompact (closure U.val) ∧ F '' closure U.val ⊆ O := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hF) z hz
  let U : OpenDomain a := ballDomain z (r / 2)
  have hsub : closure U.val ⊆ closedBall z (r / 2) := closure_ball_subset_closedBall
  refine ⟨U, mem_ball_self (by linarith),
    (isCompact_closedBall z (r / 2)).of_isClosed_subset isClosed_closure hsub, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact hball ((closedBall_subset_ball (by linarith : r / 2 < r)) (hsub hx))

/-- A genuine simple lateral point of the standard cubical cone has a
compact interior surface patch for the canonical normal-trace chart. -/
theorem exists_native_cone_lateral_patch {n : ℕ} (y : Domain ((n + 1) + 1)) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let S : Set (Domain n) := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let T : Domain (n + 1) → ℝ := fun z => (b z).2 0
    let ξ : Domain (n + 1) → Domain n := fun z => (T z)⁻¹ • (b z).1
    let Ψ : Domain (n + 1) → Domain (n + 1) := fun z =>
      b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2))
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun z =>
      e.symm (Ψ z, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2))
    0 < (e y).2 0 → (e y).2 0 < 1 → (b (e y).1).2 0 = (e y).2 0 →
    (∀ k : Fin n, |(b (e y).1).1 k| < (e y).2 0) →
    ∃ (b₀ b₁ : ℝ) (z : Domain (n + 1)) (U : OpenDomain (n + 1)),
      0 < b₀ ∧ b₀ < b₁ ∧ b₁ < 1 ∧ Γ z = y ∧ z ∈ U.val ∧
      IsCompact (closure U.val) ∧
      Ψ '' closure U.val ⊆ interior {x | T x ∈ Icc b₀ b₁ ∧ ξ x ∈ S} := by
  intro b e S T ξ Ψ Γ ht ht1 htie hstrict
  let t := (e y).2 0
  let z := b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2 * t))
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hΨz : Ψ z = (e y).1 := by
    apply b.injective
    simp only [Ψ, z, b.apply_symm_apply, PiLp.single_apply, ite_true]
    apply Prod.ext
    · rfl
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp only [PiLp.single_apply, ite_true]
      rw [htie]
      dsimp [t]
      field_simp
  have hΓz : Γ z = y := by
    apply e.injective
    simp only [Γ, e.apply_symm_apply, hΨz]
    apply Prod.ext
    · rfl
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp only [z, b.apply_symm_apply, PiLp.single_apply, ite_true]
      dsimp [t]
      field_simp
  let b₀ := t / 2
  let b₁ := (t + 1) / 2
  have hTb : T (Ψ z) = t := by simpa only [hΨz, T, t] using htie
  have hξ : ξ (Ψ z) ∈ S := by
    apply mem_iInter.mpr
    intro k
    change -1 < ξ (Ψ z) k ∧ ξ (Ψ z) k < 1
    have h := hstrict k
    rw [← abs_lt] 
    change |(T (Ψ z))⁻¹ * (b (Ψ z)).1 k| < 1
    rw [hTb, hΨz, abs_mul, abs_inv, abs_of_pos ht]
    exact (inv_mul_lt_iff₀ ht).mpr (by simpa using h)
  have hTc : Continuous T := (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
    (continuous_snd.comp b.continuous)
  have hξc : ContinuousAt ξ (Ψ z) :=
    (hTc.continuousAt.inv₀ (by rw [hTb]; exact ne_of_gt ht)).smul
      (continuous_fst.comp b.continuous).continuousAt
  have hS : IsOpen S := isOpen_iInter_of_finite fun k : Fin n =>
    isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous
  have hnhds : {x : Domain (n + 1) | T x ∈ Icc b₀ b₁ ∧ ξ x ∈ S} ∈ 𝓝 (Ψ z) := by
    have htime : T ⁻¹' Ioo b₀ b₁ ∈ 𝓝 (Ψ z) :=
      hTc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hTb]; constructor <;> dsimp [b₀, b₁] <;> linarith))
    filter_upwards [htime, hξc.preimage_mem_nhds (hS.mem_nhds hξ)] with x hx hxξ
    exact ⟨⟨hx.1.le, hx.2.le⟩, hxξ⟩
  have hsingle : Isometry (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    intro r s
    exact PiLp.edist_single_same 2 (fun _ : Fin 1 => ℝ) 0 r s
  have hΨ : Continuous Ψ := b.symm.continuous.comp
    ((continuous_fst.comp b.continuous).prodMk
      (hsingle.continuous.comp (hTc.div_const _)))
  obtain ⟨U, hzU, hU, hImage⟩ := exists_compact_open_patch_preimage hΨ isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hnhds)
  exact ⟨b₀, b₁, z, U, by dsimp [b₀]; linarith, by dsimp [b₀, b₁]; linarith,
    by dsimp [b₁]; linarith, hΓz, hzU, hU, hImage⟩

end StratificationTheory
