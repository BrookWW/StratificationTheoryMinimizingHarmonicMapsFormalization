module

public import StratificationTheory.Foundation.CubicalTripleTieFlats
public import StratificationTheory.Foundation.SobolevLocalAssembly

public section

open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- A bounded original weak pair with actual local Sobolev graphs outside
the cubical triple-tie arrangement extends across that arrangement. The
displayed map and every physical column remain the same throughout. -/
theorem memW12_of_bounded_local_sobolev_off_cubical_triple_ties {n q : ℕ}
    (c : Domain (n + 3)) {Ω : OpenDomain (n + 3)} (hΩ : Bornology.IsBounded Ω.val)
    {w : Domain (n + 3) → Ambient q} {D : Domain (n + 3) → Gradient (n + 3) q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i : Fin (n + 3), MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ B)
    (hlocal : ∀ x ∈ Ω.val,
      (¬ ∃ i j k : Fin (n + 3), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        |(x - c) j| = |(x - c) i| ∧ |(x - c) k| = |(x - c) i|) →
      ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain x r) w D) :
    MemW12 Ω w D := by
  classical
  let I := (Fin 3 ↪ Fin (n + 3)) × Bool × Bool
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 2)
  obtain ⟨Q, _hQ, hUnion⟩ := exists_cubical_triple_tie_flat_isometries n
  let P : I → Domain (n + 3) →L[ℝ] Domain 2 := fun j =>
    (ContinuousLinearMap.snd ℝ (Domain (n + 1)) (Domain 2)).comp
      (e.toContinuousLinearMap.comp (Q j).toContinuousLinearEquiv.toContinuousLinearMap)
  let Z : I → Set (Domain (n + 3)) := fun j => (fun x => P j (x - c)) ⁻¹' {(0 : Domain 2)}
  let V : OpenDomain (n + 3) :=
    ⟨Ω.val ∩ (⋃ j ∈ (Finset.univ : Finset I), Z j)ᶜ,
      Ω.property.inter (isClosed_biUnion_finset (fun j _ =>
        isClosed_singleton.preimage ((P j).continuous.comp
          (continuous_id.sub continuous_const)))).isOpen_compl⟩
  have hfinish := memW12_of_bounded_local_sobolev_off_finite_affine_flats
    (n := n + 1) (Finset.univ : Finset I) Q (fun _ => c) hΩ hw hD hB
  apply hfinish
  change ∀ x ∈ V.val, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ V.val ∧ MemW12 (ballDomain x r) w D
  intro x hx
  have hxnot : ¬ ∃ i j k : Fin (n + 3), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      |(x - c) j| = |(x - c) i| ∧ |(x - c) k| = |(x - c) i| := by
    intro htriple
    have hmem := (hUnion (x - c)).mpr htriple
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    apply hx.2
    apply mem_iUnion.mpr
    refine ⟨j, mem_iUnion.mpr ⟨Finset.mem_univ j, ?_⟩⟩
    exact hj
  obtain ⟨r, hr, hWr⟩ := hlocal x hx.1 hxnot
  obtain ⟨δ, hδ, hVball⟩ := Metric.isOpen_iff.mp V.property x hx
  have hmin : 0 < min r δ := lt_min hr hδ
  have hsub : ball x (min r δ) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r δ, hmin, (ball_subset_ball (min_le_right _ _)).trans hVball, ?_⟩
  exact ⟨hWr.1.mono hsub,
    hWr.2.1.mono_measure (Measure.restrict_mono_set volume hsub),
    fun i => (hWr.2.2 i).mono_measure (Measure.restrict_mono_set volume hsub)⟩

end StratificationTheory
