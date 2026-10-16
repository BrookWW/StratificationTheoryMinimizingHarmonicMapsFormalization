module

public import StratificationTheory.Foundation.CubicalBoundaryRadialData
public import StratificationTheory.Foundation.CubicalFrameSeamNeighborhood
public import StratificationTheory.Foundation.CubicalSimpleSeamFrame
public import StratificationTheory.Foundation.LocalWeakGradientFromCover
public import StratificationTheory.Foundation.CubicalTripleTieRemoval

public section

open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace StratificationTheory

private theorem bounded_unit_coordinate_face (d : ℕ) :
    Bornology.IsBounded (⋂ k : Fin d, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(d : ℝ) + 1, ?_⟩
  intro x hx
  have hsum : ‖x‖ ^ 2 ≤ (d : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ k : Fin d, (x k) ^ 2 ≤ ∑ _k : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have hk := (mem_unit_coordinate_face_iff x).mp hx k
        nlinarith [abs_nonneg (x k), sq_abs (x k)]
      _ = (d : ℝ) := by simp
  nlinarith [norm_nonneg x, Nat.cast_nonneg (α := ℝ) d]

private theorem exists_real_coordinate_sign (t : ℝ) :
    ∃ a : ℝ, a ^ 2 = 1 ∧ a * t = |t| := by
  by_cases ht : 0 ≤ t
  · exact ⟨1, by norm_num, by rw [one_mul, abs_of_nonneg ht]⟩
  · exact ⟨-1, by norm_num, by rw [neg_one_mul, abs_of_neg (lt_of_not_ge ht)]⟩

/-- Bounded original Sobolev data on all cube faces, with compatible original
flat L2 endpoint classes in a finite family of signed permutation frames,
produce one radial Sobolev extension on the whole cube. Its actual columns
have the exact cone energy and every common a.e. face property. -/
theorem exists_cubical_compatible_boundary_extension {n q : ℕ}
    (G : Domain ((n + 2) + 1) → Ambient q)
    (Df : (Fin ((n + 2) + 1) × Bool) → Domain (n + 2) → Gradient (n + 2) q) :
    let d := (n + 2) + 1
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 2) (m := 1)
    let J := Fin d × Bool
    let B : OpenDomain (n + 2) :=
      ⟨⋂ k : Fin (n + 2), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 2) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let S : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain d :=
      ⟨⋂ k : Fin d, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin d =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let f : J → Domain (n + 2) → Ambient q := fun j x =>
      G (cubicalSignedFaceIsometry (n + 2) j.1 j.2 (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let A₀ := cubicalSignedFaceIsometry (n + 2) (Fin.last (n + 1)).castSucc true
    let w : Equiv.Perm (Fin d) → (Fin d → Bool) → Bool → Domain (n + 2) → Ambient q :=
      fun p s side x => G (cubicalSignedPermutation d p s
        (if side then A₀ (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
          else e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    (∀ j : J, MemW12 B (f j) (Df j)) →
    ∀ Bnd : ℝ, (∀ j : J, ∀ᵐ x ∂volume.restrict B.val, ‖f j x‖ ≤ Bnd) →
    ∀ H : Equiv.Perm (Fin d) → (Fin d → Bool) → Bool →
      C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S.val)),
    (∀ p s side, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain (n + 1) =>
        w p s side (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S.val),
        H p s side ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
          (fun x => w p s side (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ p s, H p s false ⟨1, by norm_num, le_rfl⟩ = H p s true ⟨1, by norm_num, le_rfl⟩) →
    let W : Domain d → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    ∃ D : Domain d → Gradient d q,
      MemW12 Ω W D ∧
      (∫ y in Ω.val, hsNormSq (D y)) =
        ((n + 2 : ℕ) - (1 : ℝ))⁻¹ * ∑ j : J, ∫ x in B.val,
          hsNormSq (Df j x) + ‖∑ k : Fin (n + 2), x k • Df j x k‖ ^ 2 ∧
      (∫ y in Ω.val, hsNormSq (D y)) ≤
        (((n + 2 : ℕ) + (1 : ℝ)) / ((n + 2 : ℕ) - (1 : ℝ))) *
          ∑ j : J, ∫ x in B.val, hsNormSq (Df j x) ∧
      ∀ P : Ambient q → Prop, (∀ j : J, ∀ᵐ x ∂volume.restrict B.val, P (f j x)) →
        ∀ᵐ y ∂volume.restrict Ω.val, P (W y) := by
  classical
  intro d b e J B S Ω f A₀ w hface Bnd hBound H hSlices hMatch W
  have hn : 2 ≤ n + 2 := by omega
  obtain ⟨D, hWL2, hDL2, hCone, hEnergy, hEnergyBound, hProp⟩ :=
    exists_cubical_boundary_radial_data hn G Df hface
  let C : J → OpenDomain d := fun j =>
    ⟨{y | (if j.2 then y j.1 else -y j.1) ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k : Fin d, k ≠ j.1 → |y k| < (if j.2 then y j.1 else -y j.1)},
      isOpen_cubical_signed_cone j.1 j.2⟩
  have hCover : ∀ᵐ y ∂volume.restrict Ω.val, ∃ j : J, y ∈ (C j).val :=
    ae_unit_cube_mem_cubical_signed_cone hn
  have hlocal : ∀ x ∈ Ω.val,
      (¬ ∃ i j k : Fin (n + 3), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        |(x - 0) j| = |(x - 0) i| ∧ |(x - 0) k| = |(x - 0) i|) →
      ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain x r) W D := by
    intro x hx hnot
    have hnot' : ¬ ∃ i j k : Fin d, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        |x j| = |x i| ∧ |x k| = |x i| := by simpa only [sub_zero] using hnot
    have hcube := (mem_unit_coordinate_face_iff x).mp hx
    obtain ⟨i, hiPos, hcase⟩ := cubical_maximum_coordinate_dichotomy (by dsimp [d]; omega) x hnot'
    have hNeighborhood : ∃ (V : OpenDomain d) (E : Domain d → Gradient d q),
        x ∈ V.val ∧ MemW12 V W E := by
      rcases hcase with hstrict | ⟨j, hij, hji, hstrict⟩
      · obtain ⟨positive, hsign⟩ : ∃ positive : Bool, (if positive then x i else -x i) = |x i| := by
          by_cases hp : 0 ≤ x i
          · exact ⟨true, by simp [abs_of_nonneg hp]⟩
          · exact ⟨false, by simp [abs_of_neg (lt_of_not_ge hp)]⟩
        refine ⟨C (i, positive), D, ?_, hCone (i, positive)⟩
        change (if positive then x i else -x i) ∈ Ioo (0 : ℝ) 1 ∧ _
        rw [hsign]
        exact ⟨⟨hiPos, hcube i⟩, hstrict⟩
      · obtain ⟨a, ha, hai⟩ := exists_real_coordinate_sign (x i)
        obtain ⟨a', ha', haj⟩ := exists_real_coordinate_sign (x j)
        obtain ⟨p, s, ht, ht1, htie, hother⟩ := exists_cubical_simple_seam_frame x i j hij a a' ha ha'
          (hai.symm ▸ hiPos) (hai.symm ▸ hcube i) (by rw [hai, haj, hji])
          (by intro k hki hkj; rw [hai]; exact hstrict k hki hkj)
        exact exists_cubical_frame_seam_neighborhood hn G Df p s x hface
          (H p s false) (H p s true) (hSlices p s false) (hSlices p s true) (hMatch p s)
          ht ht1 htie hother
    obtain ⟨V, E, hxV, hV⟩ := hNeighborhood
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (Ω.property.inter V.property) x ⟨hx, hxV⟩
    have hsubΩ : (ballDomain x r).val ⊆ Ω.val := fun y hy => (hball hy).1
    have hsubV : (ballDomain x r).val ⊆ V.val := fun y hy => (hball hy).2
    have hE : MemW12 (ballDomain x r) W E :=
      ⟨hV.1.mono hsubV, hV.2.1.mono_measure (Measure.restrict_mono_set volume hsubV),
        fun k => (hV.2.2 k).mono_measure (Measure.restrict_mono_set volume hsubV)⟩
    exact ⟨r, hr, memW12_same_gradient_of_open_cover C
      (ae_restrict_of_ae_restrict_of_subset hsubΩ hCover) (fun j => (hCone j).1) hE⟩
  have hFull : MemW12 Ω W D := memW12_of_bounded_local_sobolev_off_cubical_triple_ties
    (0 : Domain (n + 3)) (bounded_unit_coordinate_face d) hWL2
    (fun k => (hDL2 k).mono_measure Measure.restrict_le_self) (hProp (fun z => ‖z‖ ≤ Bnd) hBound) hlocal
  exact ⟨D, hFull, hEnergy, hEnergyBound, hProp⟩

end StratificationTheory
