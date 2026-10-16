module

public import StratificationTheory.Frozen.CylinderSobolev
import StratificationTheory.Foundation.CylinderAECoordinates
import StratificationTheory.Foundation.CylinderSurfaceMeasure
import StratificationTheory.Foundation.CylinderCoordinateMeasure
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Native almost-everywhere classes of cylinder Sobolev maps

Native surface-a.e. changes of a cylinder map preserve its full finite radial
weak extension. Polar volume coordinates transport the exceptional set, and
the original weak-gradient witness remains unchanged.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

private theorem ae_unitCylinder_param_joint {n : ℕ} (hn : 0 < n) {a b : ℝ}
    {P : unitCylinder n a b → Prop}
    (hP : ∀ᵐ c ∂(Measure.euclideanHausdorffMeasure n :
      Measure (unitCylinder n a b)), P c) :
    ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ
      ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod volume,
      ∀ ht : p.2 ∈ Icc a b,
        P ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2),
          unitCylinder_param_mem p.1 ⟨p.2, ht⟩⟩ := by
  let C := unitCylinder n a b
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let p := fun z : sphere (0 : Domain n) 1 × ℝ =>
    e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2)
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Icc a b)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hp : Measurable p := by
    apply Continuous.measurable
    apply e.symm.continuous.comp
    apply Continuous.prodMk
    · exact continuous_subtype_val.comp continuous_fst
    · let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
      have heq : (fun z : sphere (0 : Domain n) 1 × ℝ =>
          EuclideanSpace.single (0 : Fin 1) z.2) = fun z => τ.symm z.2 := by
        funext z
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [τ, PiLp.equivOfUnique]
      rw [heq]
      exact τ.symm.continuous.comp continuous_snd
  have hC : MeasurableSet C := (isClosed_native_cylinder_surface_Icc n a b).measurableSet
  have hmap : Measure.map (Subtype.val : C → Domain (n + 1))
      (Measure.euclideanHausdorffMeasure n : Measure C) =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C := by
    simpa only [Subtype.range_coe] using
      (Isometry.map_euclideanHausdorffMeasure (d := n)
        (isometry_subtype_coe : Isometry (Subtype.val : C → Domain (n + 1))))
  have hambient : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n :
      Measure (Domain (n + 1))).restrict C, ∀ hy : y ∈ C, P ⟨y, hy⟩ := by
    rw [← hmap]
    apply (MeasurableEmbedding.subtype_coe hC).ae_map_iff.mpr
    filter_upwards [hP] with c hc
    intro _
    exact hc
  have hparam : ∀ᵐ z ∂σ.prod ν, ∀ hz : p z ∈ C, P ⟨p z, hz⟩ := by
    rw [← map_cylinder_surface_product_Icc_eq_native_unitCylinder hn a b] at hambient
    exact ae_of_ae_map hp.aemeasurable hambient
  have hrestrict : ∀ᵐ z ∂(σ.prod (volume : Measure ℝ)).restrict
      ((univ : Set (sphere (0 : Domain n) 1)) ×ˢ Icc a b),
      ∀ hz : p z ∈ C, P ⟨p z, hz⟩ := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hparam
  have hall := (ae_restrict_iff'
    (MeasurableSet.univ.prod (measurableSet_Icc (a := a) (b := b)))).mp hrestrict
  filter_upwards [hall] with z hz ht
  exact hz ⟨mem_univ _, ht⟩ (unitCylinder_param_mem z.1 ⟨z.2, ht⟩)

private theorem ae_normalized_cylinder_param {n : ℕ} (hn : 0 < n) {a b : ℝ}
    {P : unitCylinder n a b → Prop}
    (hP : ∀ᵐ c ∂(Measure.euclideanHausdorffMeasure n :
      Measure (unitCylinder n a b)), P c) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let V := {y : Domain (n + 1) | (e y).1 ≠ 0}
    ∀ᵐ y : V ∂(volume : Measure (Domain (n + 1))).comap (Subtype.val : V → Domain (n + 1)),
      ∀ ht : (e y.val).2 0 ∈ Icc a b,
        let x : ({(0 : Domain n)}ᶜ : Set (Domain n)) :=
          ⟨(e y.val).1, by change (e y.val).1 ≠ 0; exact y.property⟩
        let θ := (homeomorphUnitSphereProd (Domain n) x).1
        P ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) ((e y.val).2 0)),
          unitCylinder_param_mem θ ⟨(e y.val).2 0, ht⟩⟩ := by
  intro e V
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let η := Measure.volumeIoiPow (n - 1)
  let ν := (volume : Measure ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hjoint := ae_unitCylinder_param_joint hn hP
  have hprod : ∀ᵐ z : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ)
      ∂(σ.prod ν).prod η, ∀ ht : z.1.2 ∈ Icc a b,
        P ⟨e.symm (z.1.1.val, EuclideanSpace.single (0 : Fin 1) z.1.2),
          unitCylinder_param_mem z.1.1 ⟨z.1.2, ht⟩⟩ :=
    Measure.quasiMeasurePreserving_fst.ae hjoint
  have hs : MeasurePreserving
      (fun p : sphere (0 : Domain n) 1 × (Ioi (0 : ℝ) × ℝ) => ((p.1, p.2.2), p.2.1))
      (σ.prod (η.prod ν)) ((σ.prod ν).prod η) :=
    ((measurePreserving_prodAssoc σ ν η).symm MeasurableEquiv.prodAssoc).comp
      ((MeasurePreserving.id σ).prod Measure.measurePreserving_swap)
  exact (measurePreserving_native_polar_cylinder_coordinates hn).quasiMeasurePreserving.ae
    (hs.quasiMeasurePreserving.ae hprod)

/-- The full finite radial cylinder Sobolev predicate is invariant under
native physical surface-a.e. equality. The original weak columns provide
the new representative's actual weak gradient on the same neighborhood. -/
theorem memCylinderW12_congr_ae {n q : ℕ} (hn : 2 ≤ n) {a b : ℝ} (hab : a < b)
    {v v' : unitCylinder n a b → Ambient q} (hv : MemCylinderW12 hn hab v)
    (hvv' : v =ᵐ[Measure.euclideanHausdorffMeasure n] v') :
    MemCylinderW12 hn hab v' := by
  classical
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  obtain ⟨hLp, U, hS, h0, w, Dw, hW, hRay⟩ := hv
  let V := {y : Domain (n + 1) | (e y).1 ≠ 0}
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  let c : (y : Domain (n + 1)) →
      ((e y).1 ≠ 0 ∧ (e y).2 0 ∈ Ioo a b) → unitCylinder n a b := fun y hy =>
    let x : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨(e y).1, hy.1⟩
    let θ := (homeomorphUnitSphereProd (Domain n) x).1
    ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)),
      unitCylinder_param_mem θ ⟨(e y).2 0, hy.2.1.le, hy.2.2.le⟩⟩
  let w' : Domain (n + 1) → Ambient q := fun y =>
    if hy : (e y).1 ≠ 0 ∧ (e y).2 0 ∈ Ioo a b then v' (c y hy) else 0
  have hV : MeasurableSet V :=
    (e.continuous.fst.measurable (measurableSet_singleton (0 : Domain n))).compl
  have hpolar := ae_normalized_cylinder_param (by omega : 0 < n) hvv'
  have hnormAE : ∀ᵐ y ∂(volume : Measure (Domain (n + 1))).restrict V,
      ∀ hy : (e y).1 ≠ 0 ∧ (e y).2 0 ∈ Ioo a b, v (c y hy) = v' (c y hy) := by
    apply (ae_restrict_iff_subtype hV).mpr
    filter_upwards [hpolar] with y hy
    intro ht
    exact hy ⟨ht.2.1.le, ht.2.2.le⟩
  have hsub : Ω.val ⊆ V := by
    intro y hy hz
    exact h0 (hz ▸ hy.1)
  have hww' : w =ᵐ[volume.restrict Ω.val] w' := by
    filter_upwards [hnormAE.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub)),
      ae_restrict_mem Ω.property.measurableSet] with y hy hΩ
    have hyv : (e y).1 ≠ 0 ∧ (e y).2 0 ∈ Ioo a b := ⟨hsub hΩ, hΩ.2⟩
    let x : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨(e y).1, hyv.1⟩
    let p := homeomorphUnitSphereProd (Domain n) x
    have hp : p.2.val • p.1.val = (e y).1 := by
      have heq := congrArg (fun z : ({(0 : Domain n)}ᶜ : Set (Domain n)) => z.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply x)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using heq
    have hcTime : (e (c y hyv).val).2 0 ∈ Ioo a b := by
      change (e (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)))).2 0 ∈ Ioo a b
      rw [e.apply_symm_apply]
      simpa only [PiLp.single_apply, ite_true] using hyv.2
    have hcRad : p.2.val • (e (c y hyv).val).1 ∈ U.val := by
      change p.2.val • (e (e.symm (p.1.val,
        EuclideanSpace.single (0 : Fin 1) ((e y).2 0)))).1 ∈ U.val
      rw [e.apply_symm_apply, hp]
      exact hΩ.1
    have hwy : w y = v (c y hyv) := by
      have hraw := hRay ⟨p.2.val, p.2.property⟩ (c y hyv) hcTime hcRad
      change w (e.symm (p.2.val • (e (c y hyv).val).1, (e (c y hyv).val).2)) = _ at hraw
      have hc : e (c y hyv).val =
          (p.1.val, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) := e.apply_symm_apply _
      rw [hc, hp] at hraw
      rw [cylinder_coordinates_inverse_left n y] at hraw
      exact hraw
    calc
      w y = v (c y hyv) := hwy
      _ = v' (c y hyv) := hy hyv
      _ = w' y := (show w' y = v' (c y hyv) from dif_pos hyv).symm
  refine ⟨hLp.ae_eq hvv', U, hS, h0, w', Dw,
    hW.congr_ae hww' (EventuallyEq.refl _ _), ?_⟩
  intro ρ z ht _hx
  let y := e.symm (ρ.val • (e z.val).1, (e z.val).2)
  have hθ : ‖(e z.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp z.property.1
  have hrzero : ρ.val • (e z.val).1 ≠ 0 := by
    intro hz
    have hnrm := congrArg norm hz
    rw [norm_smul, Real.norm_of_nonneg ρ.property.le, hθ, mul_one, norm_zero] at hnrm
    exact ρ.property.ne' hnrm
  have hy : (e y).1 ≠ 0 ∧ (e y).2 0 ∈ Ioo a b := by
    dsimp only [y]
    rw [e.apply_symm_apply]
    exact ⟨hrzero, ht⟩
  have hcy : c y hy = z := by
    let θ : sphere (0 : Domain n) 1 := ⟨(e z.val).1, z.property.1⟩
    let p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) := (θ, ⟨ρ.val, ρ.property⟩)
    let x : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨(e y).1, hy.1⟩
    have hx : x = (homeomorphUnitSphereProd (Domain n)).symm p := by
      apply Subtype.ext
      change (e y).1 = _
      dsimp only [y]
      rw [e.apply_symm_apply]
      simp only [homeomorphUnitSphereProd_symm_apply_coe, p, θ]
    apply Subtype.ext
    change e.symm (((homeomorphUnitSphereProd (Domain n) x).1).val,
      EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = z.val
    rw [hx, Homeomorph.apply_symm_apply]
    change e.symm ((e z.val).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = z.val
    dsimp only [y]
    rw [e.apply_symm_apply]
    exact cylinder_coordinates_inverse_left n z.val
  change w' y = v' z
  rw [show w' y = v' (c y hy) from dif_pos hy, hcy]

/-- Full finite cylinder Sobolev membership depends only on the actual
native physical surface-a.e. class, in both directions. -/
theorem memCylinderW12_congr_ae_iff {n q : ℕ} (hn : 2 ≤ n) {a b : ℝ} (hab : a < b)
    {v v' : unitCylinder n a b → Ambient q}
    (hvv' : v =ᵐ[Measure.euclideanHausdorffMeasure n] v') :
    MemCylinderW12 hn hab v ↔ MemCylinderW12 hn hab v' :=
  ⟨fun hv => memCylinderW12_congr_ae hn hab hv hvv',
    fun hv => memCylinderW12_congr_ae hn hab hv hvv'.symm⟩

end StratificationTheory
