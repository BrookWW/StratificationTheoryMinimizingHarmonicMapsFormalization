module

public import StratificationTheory.Foundation.CoordinateGridPairFlats
public import StratificationTheory.Foundation.SobolevLocalAssembly

public section

open HarmonicMaps MeasureTheory Set Filter Metric

namespace StratificationTheory

/-- The actual intersections of finitely many distinct coordinate grid
directions are removable for a bounded original pair with genuine local
weak graphs off that grid skeleton. -/
theorem memW12_of_bounded_local_sobolev_off_coordinate_grid_intersections {n q : ℕ}
    (T : Fin (n + 2) → Finset ℝ) {Ω : OpenDomain (n + 2)} (hΩ : Bornology.IsBounded Ω.val)
    {w : Domain (n + 2) → Ambient q} {D : Domain (n + 2) → Gradient (n + 2) q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i, MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ B)
    (hlocal : ∀ x ∈ Ω.val,
      (¬ ∃ i j : Fin (n + 2), i ≠ j ∧ x i ∈ T i ∧ x j ∈ T j) →
      ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain x r) w D) : MemW12 Ω w D := by
  classical
  let P := {p : Fin (n + 2) × Fin (n + 2) // p.1 ≠ p.2}
  let I := Σ p : P, (T p.val.1) × (T p.val.2)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 2)
  have hEach (p : P) := exists_coordinate_grid_pair_flat_isometry p.val.1 p.val.2 p.property
  choose Q hQ using hEach
  let QI : I → Domain (n + 2) ≃ₗᵢ[ℝ] Domain (n + 2) := fun k => Q k.1
  let c : I → Domain (n + 2) := fun k =>
    EuclideanSpace.single k.1.val.1 k.2.1.val + EuclideanSpace.single k.1.val.2 k.2.2.val
  let L : I → Domain (n + 2) →L[ℝ] Domain 2 := fun k =>
    (ContinuousLinearMap.snd ℝ (Domain n) (Domain 2)).comp
      (e.toContinuousLinearMap.comp (QI k).toContinuousLinearEquiv.toContinuousLinearMap)
  let Z : I → Set (Domain (n + 2)) := fun k => (fun x => L k (x - c k)) ⁻¹' {(0 : Domain 2)}
  have hUnion (x : Domain (n + 2)) :
      x ∈ ⋃ k ∈ (Finset.univ : Finset I), Z k ↔
        ∃ i j : Fin (n + 2), i ≠ j ∧ x i ∈ T i ∧ x j ∈ T j := by
    constructor
    · intro hx
      obtain ⟨k, _hk, hxk⟩ := mem_iUnion₂.mp hx
      have hzero : (e (Q k.1 (x - c k))).2 = 0 := hxk
      have hp := (hQ k.1 k.2.1.val k.2.2.val x).mp hzero
      exact ⟨k.1.val.1, k.1.val.2, k.1.property, hp.1.symm ▸ k.2.1.property, hp.2.symm ▸ k.2.2.property⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      let k : I := ⟨⟨(i, j), hij⟩, ⟨⟨x i, hi⟩, ⟨x j, hj⟩⟩⟩
      apply mem_iUnion₂.mpr
      refine ⟨k, Finset.mem_univ k, ?_⟩
      exact (hQ k.1 k.2.1.val k.2.2.val x).mpr ⟨rfl, rfl⟩
  let V : OpenDomain (n + 2) :=
    ⟨Ω.val ∩ (⋃ k ∈ (Finset.univ : Finset I), Z k)ᶜ,
      Ω.property.inter (isClosed_biUnion_finset (fun k _ =>
        isClosed_singleton.preimage ((L k).continuous.comp
          (continuous_id.sub continuous_const)))).isOpen_compl⟩
  apply memW12_of_bounded_local_sobolev_off_finite_affine_flats
    (Finset.univ : Finset I) QI c hΩ hw hD hB
  change ∀ x ∈ V.val, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ V.val ∧ MemW12 (ballDomain x r) w D
  intro x hx
  have hnot : ¬ ∃ i j : Fin (n + 2), i ≠ j ∧ x i ∈ T i ∧ x j ∈ T j :=
    fun h => hx.2 ((hUnion x).mpr h)
  obtain ⟨r, hr, hWr⟩ := hlocal x hx.1 hnot
  obtain ⟨δ, hδ, hVball⟩ := Metric.isOpen_iff.mp V.property x hx
  have hsub : ball x (min r δ) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r δ, lt_min hr hδ, (ball_subset_ball (min_le_right _ _)).trans hVball,
    hWr.1.mono hsub, hWr.2.1.mono_measure (Measure.restrict_mono_set volume hsub), ?_⟩
  exact fun i => (hWr.2.2 i).mono_measure (Measure.restrict_mono_set volume hsub)

end StratificationTheory
