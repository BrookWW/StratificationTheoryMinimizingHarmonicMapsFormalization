module

public import StratificationTheory.Foundation.CylinderPointCoordinates
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
public import StratificationTheory.Foundation.LpClosedTargets
public import Mathlib.Topology.ContinuousMap.Algebra
import StratificationTheory.Foundation.CylinderSurfaceMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Almost-everywhere properties of native cylinder slices

Native physical-cylinder almost-everywhere properties hold on almost every
angular slice at almost every time. The coordinate transfer uses the exact
native surface-product identity and leaves endpoint values unspecified.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- A native-cylinder a.e. property holds on native angular a.e. points at
almost every closed-interval time. -/
theorem ae_unitCylinder_param {n : ℕ} (hn : 0 < n) {a b : ℝ}
    {P : unitCylinder n a b → Prop}
    (hP : ∀ᵐ c ∂(Measure.euclideanHausdorffMeasure n :
      Measure (unitCylinder n a b)), P c) :
    ∀ᵐ t ∂volume, ∀ ht : t ∈ Icc a b,
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        P ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t),
          unitCylinder_param_mem θ ⟨t, ht⟩⟩ := by
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
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hparam
  have hslices := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hslices] with t ht htI
  filter_upwards [ht htI] with θ hθ
  exact hθ (unitCylinder_param_mem θ ⟨t, htI⟩)

/-- Continuous native-L2 representatives of native-a.e. equal cylinder maps
agree on the whole closed interval, including both endpoint traces. -/
theorem continuous_unitCylinder_representatives_eq_of_ae {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (hab : a < b) (v w : unitCylinder n a b → Ambient q)
    (hvw : v =ᵐ[Measure.euclideanHausdorffMeasure n] w) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun p =>
      ⟨e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val), unitCylinder_param_mem p.1 p.2⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∀ H K : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩)))) →
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => w (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
          K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => w (c (θ, ⟨t, ht.1.le, ht.2.le⟩)))) →
      H = K := by
  intro e c σ H K hH hK
  have hs := ae_unitCylinder_param hn hvw
  have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      (H - K) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ)) := by
    filter_upwards [hH, hK, hs] with t hHt hKt hst ht
    obtain ⟨hvt, hHv⟩ := hHt ht
    obtain ⟨hwt, hKw⟩ := hKt ht
    have hclass := hvt.toLp_congr hwt (hst ⟨ht.1.le, ht.2.le⟩)
    change H ⟨t, ht.1.le, ht.2.le⟩ - K ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ))
    rw [mem_singleton_iff, sub_eq_zero]
    exact hHv.trans (hclass.trans hKw.symm)
  have hall := continuous_interval_mem_closed_of_ae hab (H - K) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro t
  exact sub_eq_zero.mp (Set.mem_singleton_iff.mp (hall t))

/-- A continuous native-L2 representative of a cylinder map with native-a.e.
values in a closed set retains that constraint at every time, including endpoints. -/
theorem continuous_unitCylinder_representative_mem_closed {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    {S : Set (Ambient q)} (hS : IsClosed S)
    (hvS : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)), v y ∈ S) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun p =>
      ⟨e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val), unitCylinder_param_mem p.1 p.2⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∀ H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩)))) →
      ∀ t : Icc a b, ∀ᵐ θ ∂σ, H t θ ∈ S := by
  intro e c σ H hH
  apply continuous_interval_lp_two_ae_mem_closed hS hab H
  have hs := ae_unitCylinder_param hn hvS
  filter_upwards [hH, hs] with t hHt hst ht
  obtain ⟨hvt, hHv⟩ := hHt ht
  rw [hHv]
  filter_upwards [hvt.coeFn_toLp, hst ⟨ht.1.le, ht.2.le⟩] with θ hθ hmem
  rw [hθ]
  exact hmem

end StratificationTheory
