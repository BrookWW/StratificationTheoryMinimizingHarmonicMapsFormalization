module

public import StratificationTheory.Foundation.PiecewiseCellGlobalRectangleTrace
public import StratificationTheory.Foundation.UniformGridCellCoordinates

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- The actual weak map on a spatial mesh subdomain times one time interval
has its original global temporal endpoints, as determined by the actual
physical cell curves. Spatial intersections and all restricted trace
qualifications are constructed internally. -/
theorem exists_uniform_mesh_global_temporal_trace {n N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (U : OpenDomain (n + 1)) (hUSub : U.val ⊆ (uniformGridBox (n + 1) N ε).val)
    {a b : ℝ} (hab : a < b)
    (u : (Fin (n + 1) → Fin N) → Domain ((n + 1) + 1) → Ambient q)
    (W : Domain ((n + 1) + 1) → Ambient q) (D : Domain ((n + 1) + 1) → Gradient ((n + 1) + 1) q)
    (g₀ g₁ : Domain (n + 1) → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Ω : OpenDomain ((n + 1) + 1) :=
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    MemW12 Ω W D →
    (∀ z x, x ∈ U.val → x ∈ (uniformGridCell (n + 1) N ε z).val → ∀ t ∈ Ioo a b,
      W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
        u z (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) →
    ∀ K : ∀ z : Fin (n + 1) → Fin N,
      C(Icc a b, Lp (Ambient q) 2 (volume.restrict (uniformGridCell (n + 1) N ε z).val)),
    (∀ z, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x : Domain (n + 1) => u z (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
          (volume.restrict (uniformGridCell (n + 1) N ε z).val),
        K z ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u z (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ z, (K z ⟨a, le_rfl, hab.le⟩ : Domain (n + 1) → Ambient q)
      =ᵐ[volume.restrict (uniformGridCell (n + 1) N ε z).val] g₀) →
    (∀ z, (K z ⟨b, hab.le, le_rfl⟩ : Domain (n + 1) → Ambient q)
      =ᵐ[volume.restrict (uniformGridCell (n + 1) N ε z).val] g₁) →
    ∃ H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hs : MemLp (fun x : Domain (n + 1) => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      (∃ hg₀ : MemLp g₀ 2 (volume.restrict U.val), H ⟨a, le_rfl, hab.le⟩ = hg₀.toLp g₀) ∧
      (∃ hg₁ : MemLp g₁ 2 (volume.restrict U.val), H ⟨b, hab.le, le_rfl⟩ = hg₁.toLp g₁) ∧
      ∀ J : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hs : MemLp (fun x : Domain (n + 1) => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → J = H := by
  classical
  intro e Ω hW hPoint K hK hK₀ hK₁
  have hUbound : Bornology.IsBounded U.val := by
    apply Bornology.IsBounded.subset ?_ hUSub
    have hSet : (uniformGridBox (n + 1) N ε).val =
        {x : Domain (n + 1) | ∀ i, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)} :=
      Set.ext fun x => mem_uniformGridBox_iff _ _ _ x
    rw [hSet]
    exact isBounded_positive_coordinate_box _ _
  letI : IsFiniteMeasure ((volume : Measure (Domain (n + 1))).restrict U.val) :=
    isFiniteMeasure_restrict.mpr hUbound.measure_lt_top.ne
  let C : (Fin (n + 1) → Fin N) → OpenDomain (n + 1) := fun z =>
    ⟨U.val ∩ (uniformGridCell (n + 1) N ε z).val,
      U.property.inter (uniformGridCell (n + 1) N ε z).property⟩
  have hCover : ∀ᵐ x ∂volume.restrict U.val, ∃ z, x ∈ (C z).val := by
    have h := ae_uniform_grid_cell_cover n N hε
    have hSet : (uniformGridBox (n + 1) N ε).val =
        {x : Domain (n + 1) | ∀ i, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)} :=
      Set.ext fun x => mem_uniformGridBox_iff _ _ _ x
    rw [← hSet] at h
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUSub h, ae_restrict_mem U.property.measurableSet] with x hx hxU
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hxU, (mem_uniformGridCell_iff _ _ _ z x).mpr hz⟩
  have hEach (z : Fin (n + 1) → Fin N) :
      ∃ J : C(Icc a b, Lp (Ambient q) 2 (volume.restrict (C z).val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hs : MemLp (fun x : Domain (n + 1) => u z (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict (C z).val),
            J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u z (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        ((J ⟨a, le_rfl, hab.le⟩ : Domain (n + 1) → Ambient q) =ᵐ[volume.restrict (C z).val] g₀) ∧
        ((J ⟨b, hab.le, le_rfl⟩ : Domain (n + 1) → Ambient q) =ᵐ[volume.restrict (C z).val] g₁) := by
    let μ := (volume : Measure (Domain (n + 1))).restrict (C z).val
    let ν := (volume : Measure (Domain (n + 1))).restrict (uniformGridCell (n + 1) N ε z).val
    have hμν : μ ≤ ν := Measure.restrict_mono_set volume (fun _ hx => hx.2)
    let L : Lp (Ambient q) 2 ν →L[ℝ] Lp (Ambient q) 2 μ := Lp.LpToLpOfMeasureLeSMul
      (c := (1 : ℝ≥0∞)) (by norm_num) (by simpa only [one_smul] using hμν)
    let J : C(Icc a b, Lp (Ambient q) 2 μ) := ⟨fun t => L (K z t), L.continuous.comp (K z).continuous⟩
    refine ⟨J, ?_, ?_, ?_⟩
    · filter_upwards [hK z] with t ht htI
      obtain ⟨hs, hClass⟩ := ht htI
      have hsmall := hs.mono_measure hμν
      refine ⟨hsmall, ?_⟩
      change L (K z ⟨t, htI.1.le, htI.2.le⟩) = _
      rw [hClass]
      exact lp_two_measure_restriction_toLp hμν _ hs hsmall
    · have hCoe := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
        (by norm_num) (show μ ≤ (1 : ℝ≥0∞) • ν by simpa only [one_smul] using hμν) (K z ⟨a, le_rfl, hab.le⟩)
      exact hCoe.trans ((Measure.absolutelyContinuous_of_le hμν).ae_eq (hK₀ z))
    · have hCoe := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
        (by norm_num) (show μ ≤ (1 : ℝ≥0∞) • ν by simpa only [one_smul] using hμν) (K z ⟨b, hab.le, le_rfl⟩)
      exact hCoe.trans ((Measure.absolutelyContinuous_of_le hμν).ae_eq (hK₁ z))
  choose J hJ hJ₀ hJ₁ using hEach
  exact exists_global_rectangle_trace_of_piecewise_cell_traces U C (fun _ _ hx => hx.1) hCover hab u W D g₀ g₁ hW
    (fun z x hx t ht => hPoint z x hx.1 hx.2 t ht) J hJ hJ₀ hJ₁

end StratificationTheory
