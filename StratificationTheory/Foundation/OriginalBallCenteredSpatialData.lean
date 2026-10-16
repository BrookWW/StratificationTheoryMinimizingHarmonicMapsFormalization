module

public import HarmonicMaps.SobolevRestriction
public import StratificationTheory.Foundation.GridCubeBallContainment
public import StratificationTheory.Foundation.NativeCoordinateCubeOpen

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Original ball Sobolev pairs and their original target values restrict
to the entire centered spatial cube used by the quantitative connector. -/
theorem original_ball_centered_cube_data {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    (N : Set (Ambient q))
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N) :
    let U : OpenDomain (n + 2) :=
      ⟨⋂ j : Fin (n + 2), (EuclideanSpace.proj j) ⁻¹' Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ),
        isOpen_iInter_of_finite (fun j : Fin (n + 2) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    (∀ l, MemW12 U (w l) (Dw l)) ∧
      ∀ l, ∀ᵐ x ∂volume.restrict U.val, w l x ∈ N := by
  intro U
  have hSub : U.val ⊆ ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
    intro x hx
    have hBound : ∀ j : Fin (n + 2), |x j| ≤ 1 := by
      intro j
      have hj := mem_iInter.mp hx j
      change -(3 / 4 : ℝ) < x j ∧ x j < (3 / 4 : ℝ) at hj
      apply abs_le.mpr
      constructor <;> linarith [hj.1, hj.2]
    have hn := euclidean_norm_le_dim_of_coordinate_bound x hBound
    rw [mem_ball_zero_iff]
    push_cast at hn
    linarith
  constructor
  · intro l
    exact ⟨(hSob l).1.mono hSub,
      (hSob l).2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => ((hSob l).2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  · intro l
    exact ae_restrict_of_ae_restrict_of_subset hSub (hTarget l)

end StratificationTheory
