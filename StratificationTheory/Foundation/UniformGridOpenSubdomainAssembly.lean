module

public import StratificationTheory.Foundation.UniformGridAdjacentGluing
public import StratificationTheory.Foundation.FinitePiecewiseSobolevFields
public import StratificationTheory.Foundation.CoordinateGridSkeletonRemoval
public import StratificationTheory.Foundation.LocalWeakGradientFromCover

public section

open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace StratificationTheory

/-- On any open subdomain of the actual mesh box, bounded original cell maps with
matching original native face trace classes on every shared face meeting the subdomain produce their literal global
piecewise Sobolev pair. Shared faces are glued internally and the actual
finite codimension-two grid skeleton is removed. Native energy is additive. -/
theorem memW12_uniform_grid_piecewise_on_open_subdomain {n N q : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (Ω : OpenDomain (n + 2)) (hΩsub : Ω.val ⊆ (uniformGridBox (n + 2) N ε).val)
    (u : (Fin (n + 2) → Fin N) → Domain (n + 2) → Ambient q)
    (A : (Fin (n + 2) → Fin N) → Domain (n + 2) → Gradient (n + 2) q)
    (hu : ∀ z, MemW12 (uniformGridCell (n + 2) N ε z) (u z) (A z))
    (Bnd : ℝ) (hBound : ∀ z, ∀ᵐ x ∂volume.restrict (uniformGridCell (n + 2) N ε z).val,
      ‖u z x‖ ≤ Bnd)
    (hTrace : ∀ (i : Fin (n + 2)) (z : Fin (n + 2) → Fin N) (hzi : 0 < (z i).val),
      (∃ x ∈ Ω.val, x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) →
      let k : Fin N := ⟨(z i).val - 1, by omega⟩
      let zm := Function.update z i k
      let U := uniformGridTransverseCell (n + 1) N ε i z
      let Q := cubicalSignedFaceIsometry (n + 1) i true
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
      let a := (k.val : ℝ) * ε
      let b := ((z i).val : ℝ) * ε
      let c := (((z i).val : ℝ) + 1) * ε
      ∃ (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
        (K : C(Icc b c, Lp (Ambient q) 2 (volume.restrict U.val))),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hs : MemLp (fun x : Domain (n + 1) => u zm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u zm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b c,
          ∃ hs : MemLp (fun x : Domain (n + 1) => u z (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
            K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u z (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ hab : a < b, ∀ hbc : b < c, H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbc.le⟩) :
    let C : (Fin (n + 2) → Fin N) → OpenDomain (n + 2) := fun z =>
      ⟨Ω.val ∩ (uniformGridCell (n + 2) N ε z).val,
        Ω.property.inter (uniformGridCell (n + 2) N ε z).property⟩
    let W : Domain (n + 2) → Ambient q := fun x => ∑ z : Fin (n + 2) → Fin N, (C z).val.indicator (u z) x
    let D : Domain (n + 2) → Gradient (n + 2) q := fun x => ∑ z : Fin (n + 2) → Fin N, (C z).val.indicator (A z) x
    MemW12 Ω W D ∧
      (∀ z x, x ∈ (C z).val → W x = u z x ∧ D x = A z x) ∧
      (∫ x in Ω.val, hsNormSq (D x)) =
        ∑ z : Fin (n + 2) → Fin N, ∫ x in (C z).val, hsNormSq (A z x) ∧
      ∀ P : Ambient q → Prop,
        (∀ z, ∀ᵐ x ∂volume.restrict (C z).val, P (u z x)) →
        ∀ᵐ x ∂volume.restrict Ω.val, P (W x) := by
  classical
  intro C W D
  have hDisj : Pairwise fun z w : Fin (n + 2) → Fin N => Disjoint (C z).val (C w).val := by
    intro z w hzw
    apply disjoint_left.mpr
    intro x hxz hxw
    exact disjoint_left.mp (pairwise_disjoint_uniform_grid_cells (n + 2) N hε hzw)
      ((mem_uniformGridCell_iff _ _ _ z x).mp hxz.2) ((mem_uniformGridCell_iff _ _ _ w x).mp hxw.2)
  have hGridSet : (uniformGridBox (n + 2) N ε).val =
      {x : Domain (n + 2) | ∀ i, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)} :=
    Set.ext fun x => mem_uniformGridBox_iff (n + 2) N ε x
  have hCover : ∀ᵐ x ∂volume.restrict Ω.val, ∃ z : Fin (n + 2) → Fin N, x ∈ (C z).val := by
    have h := ae_uniform_grid_cell_cover (n + 1) N hε
    rw [← hGridSet] at h
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩsub h,
      ae_restrict_mem Ω.property.measurableSet] with x hx hxΩ
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hxΩ, (mem_uniformGridCell_iff _ _ _ z x).mpr hz⟩
  have hCell (z : Fin (n + 2) → Fin N) : MemW12 (C z) (u z) (A z) :=
    ⟨(hu z).1.mono (fun _ hx => hx.2),
      (hu z).2.1.mono_measure (Measure.restrict_mono_set volume (fun _ hx => hx.2)),
      fun j => ((hu z).2.2 j).mono_measure (Measure.restrict_mono_set volume (fun _ hx => hx.2))⟩
  obtain ⟨hWL2, hDL2, hEach, hPoint, hEnergy, hProp⟩ :=
    finite_piecewise_sobolev_fields Ω.val C hDisj (fun _ _ hx => hx.1) hCover u A hCell
  have hBoundCell (z : Fin (n + 2) → Fin N) : ∀ᵐ x ∂volume.restrict (C z).val, ‖u z x‖ ≤ Bnd :=
    ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.2) (hBound z)
  let cuts : Finset ℝ := Finset.univ.image (fun k : Fin N => (k.val : ℝ) * ε)
  have hLocal : ∀ x ∈ Ω.val,
      (¬ ∃ i j : Fin (n + 2), i ≠ j ∧ x i ∈ cuts ∧ x j ∈ cuts) →
      ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain x r) W D := by
    intro x hx hnot
    have hxBox := (mem_uniformGridBox_iff _ _ _ x).mp (hΩsub hx)
    have hCase := uniform_grid_cell_or_simple_face hε x hxBox hnot
    have hNeighborhood : ∃ (V : OpenDomain (n + 2)) (E : Domain (n + 2) → Gradient (n + 2) q),
        x ∈ V.val ∧ MemW12 V W E := by
      rcases hCase with ⟨z, hz⟩ | ⟨i, z, hzi, hxi, hother⟩
      · exact ⟨C z, D, ⟨hx, (mem_uniformGridCell_iff _ _ _ z x).mpr hz⟩, hEach z⟩
      · let k : Fin N := ⟨(z i).val - 1, by omega⟩
        let zm := Function.update z i k
        let U := uniformGridTransverseCell (n + 1) N ε i z
        let Q := cubicalSignedFaceIsometry (n + 1) i true
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
        let a := (k.val : ℝ) * ε
        let b := ((z i).val : ℝ) * ε
        let c := (((z i).val : ℝ) + 1) * ε
        let R := fun l r : ℝ => (⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo l r},
          ((U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩ : OpenDomain (n + 2))
        obtain ⟨H, K, hH, hK, hMatch⟩ := hTrace i z hzi ⟨x, hx, hxi, hother⟩
        obtain ⟨hGlue, hMinus, hPlus⟩ := uniformGrid_adjacent_cell_gluing hε i z hzi
          (u zm) (u z) (A zm) (A z) (hu zm) (hu z) H K hH hK hMatch
        have hxR : x ∈ (R a c).val := uniformGrid_shared_face_point hε i z hzi x hxi hother
        have hZero : ∀ᵐ y : Domain (n + 2) ∂volume, (e (Q.symm y)).2 0 ≠ b :=
          Q.symm.measurePreserving.quasiMeasurePreserving.ae (ae_native_time_ne (n + 1) b)
        let V : OpenDomain (n + 2) := ⟨Ω.val ∩ (R a c).val, Ω.property.inter (R a c).property⟩
        have hGlueV : MemW12 V (fun y => if (e (Q.symm y)).2 0 < b then u zm y else u z y)
            (fun y j => if (e (Q.symm y)).2 0 < b then A zm y j else A z y j) :=
          ⟨hGlue.1.mono (fun _ hy => hy.2),
            hGlue.2.1.mono_measure (Measure.restrict_mono_set volume (fun _ hy => hy.2)),
            fun j => (hGlue.2.2 j).mono_measure (Measure.restrict_mono_set volume (fun _ hy => hy.2))⟩
        have hMap : (fun y => if (e (Q.symm y)).2 0 < b then u zm y else u z y)
            =ᵐ[volume.restrict V.val] W := by
          filter_upwards [ae_restrict_of_ae hZero, ae_restrict_mem V.property.measurableSet] with y hne hy
          have hyR := hy.2
          by_cases ht : (e (Q.symm y)).2 0 < b
          · rw [if_pos ht]
            have hyM : y ∈ (R a b).val := ⟨hyR.1, hyR.2.1, ht⟩
            have hyCell : y ∈ (C zm).val := ⟨hy.1, hMinus ▸ hyM⟩
            exact (hPoint zm y hyCell).1.symm
          · rw [if_neg ht]
            have ht' : b < (e (Q.symm y)).2 0 := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm hne)
            have hyP : y ∈ (R b c).val := ⟨hyR.1, ht', hyR.2.2⟩
            have hyCell : y ∈ (C z).val := ⟨hy.1, hPlus ▸ hyP⟩
            exact (hPoint z y hyCell).1.symm
        exact ⟨V, _, ⟨hx, hxR⟩, hGlueV.congr_ae hMap (EventuallyEq.refl _ _)⟩
    obtain ⟨V, E, hxV, hV⟩ := hNeighborhood
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (Ω.property.inter V.property) x ⟨hx, hxV⟩
    have hsubΩ : (ballDomain x r).val ⊆ Ω.val := fun y hy => (hball hy).1
    have hsubV : (ballDomain x r).val ⊆ V.val := fun y hy => (hball hy).2
    have hBall : MemW12 (ballDomain x r) W E :=
      ⟨hV.1.mono hsubV, hV.2.1.mono_measure (Measure.restrict_mono_set volume hsubV),
        fun j => (hV.2.2 j).mono_measure (Measure.restrict_mono_set volume hsubV)⟩
    exact ⟨r, hr, memW12_same_gradient_of_open_cover C
      (ae_restrict_of_ae_restrict_of_subset hsubΩ hCover) (fun z => (hEach z).1) hBall⟩
  have hBoundΩ : Bornology.IsBounded Ω.val := by
    apply Bornology.IsBounded.subset ?_ hΩsub
    rw [hGridSet]
    exact isBounded_positive_coordinate_box (n + 2) ((N : ℝ) * ε)
  have hFull : MemW12 Ω W D := memW12_of_bounded_local_sobolev_off_coordinate_grid_intersections
    (fun _ => cuts) hBoundΩ hWL2 (fun j => (hDL2 j).mono_measure Measure.restrict_le_self)
      (hProp (fun z => ‖z‖ ≤ Bnd) hBoundCell) hLocal
  exact ⟨hFull, hPoint, hEnergy, hProp⟩

end StratificationTheory
