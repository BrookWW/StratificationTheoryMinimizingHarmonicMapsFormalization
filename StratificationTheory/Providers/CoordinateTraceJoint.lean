module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra
import StratificationTheory.Foundation.CoordinateL2Trace
import StratificationTheory.Foundation.CoordinateTraceRestrictions
import StratificationTheory.Foundation.CoordinateLeftSobolevSlices
import StratificationTheory.Foundation.CylinderRawTime

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
open StratificationTheory
namespace StratificationTheory.Providers.CoordinateTraceJoint

private theorem coordinate_ball_trace_existsUnique {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (_hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (U : OpenDomain n)
    {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ U.val, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ := (volume : Measure (Domain n)).restrict U.val
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp
          (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
  intro e σ
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hΩsub : Ω.val ⊆ ball z R := by
    intro y hy
    have h := hrect (e y).1 hy.1 ((e y).2 0) hy.2
    rwa [cylinder_coordinates_inverse_left n y] at h
  have hΩfinite : (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hΩsub) measure_ball_lt_top).ne
  have hΩmeasure : (volume : Measure (Domain (n + 1))) Ω.val =
      (volume : Measure (Domain n)) U.val * ENNReal.ofReal (b - a) := by
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo,
      Real.volume_Ioo]
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := by
    intro htop
    apply hΩfinite
    rw [hΩmeasure, htop, ENNReal.top_mul (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne']
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr hUfinite
  have hW : MemW12 Ω u Du :=
    ⟨hu.1.mono hΩsub, hu.2.1.mono_measure (Measure.restrict_mono_set volume hΩsub),
      fun i => (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hΩsub)⟩
  have hm := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage Ω.property.measurableSet
  have hpre : (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ⁻¹' Ω.val = U.val ×ˢ Ioo a b := by
    ext p
    simp only [Ω, mem_preimage, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply,
      PiLp.single_apply, ↓reduceIte, mem_prod]
  rw [hpre, ← Measure.prod_restrict] at hm
  let f : Domain n × ℝ → Ambient q := fun p =>
    u (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  let g : Domain n × ℝ → Ambient q := fun p =>
    Du (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) (Fin.natAdd n (0 : Fin 1))
  have hf : MemLp f 2 (σ.prod (volume.restrict (Ioo a b))) := hW.2.1.comp_measurePreserving hm
  have hg : MemLp g 2 (σ.prod (volume.restrict (Ioo a b))) :=
    (hW.2.2 (Fin.natAdd n (0 : Fin 1))).comp_measurePreserving hm
  have htime : (volume : Measure ℝ).restrict (Icc a b) = volume.restrict (Ioo a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hfC : MemLp f 2 (σ.prod (volume.restrict (Icc a b))) := by rwa [htime]
  have hgC : MemLp g 2 (σ.prod (volume.restrict (Icc a b))) := by rwa [htime]
  apply exists_unique_finite_lp_continuous_representative_of_raw_time_identity σ hab hfC hgC
  intro φ hφ hcφ hsφ
  have hae := MemW12.cylinder_time_test_ae U hUfinite hW hφ hcφ hsφ
  filter_upwards [hae] with x hx
  have hφL : MemLp φ ∞ (volume.restrict (Ioo a b)) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφL : MemLp (deriv φ) ∞ (volume.restrict (Ioo a b)) :=
    (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hcφ.deriv _
  have hleft : Integrable (fun t => deriv φ t • f (x, t)) (volume.restrict (Ioo a b)) :=
    hx.1.smul_of_top_right hdφL
  have hright : Integrable (fun t => φ t • g (x, t)) (volume.restrict (Ioo a b)) :=
    hx.2.1.smul_of_top_right hφL
  have hid := hx.2.2.2
  change (∫ t in Ioo a b, deriv φ t • f (x, t) + φ t • g (x, t)) = 0 at hid
  rw [integral_add hleft hright] at hid
  rw [htime]
  exact eq_neg_iff_add_eq_zero.mpr hid

private theorem ae_flat_sobolev_cut {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (U : OpenDomain n)
    {a b : ℝ} (_hab : a < b)
    (hrect : ∀ x ∈ U.val, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ᵐ t ∂volume, ∀ _ht : t ∈ Ioo a b,
      MemW12 U (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
        (fun x i => Du (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) (Fin.castAdd 1 i)) := by
  intro e
  let S : Set (Domain 1) := {t | t 0 ∈ Ioo a b}
  have hS : MeasurableSet S := measurableSet_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable
  have hrect' : ∀ t ∈ S, ∀ x ∈ U.val, e.symm (x, t) ∈ ball z R := by
    intro t ht x hx
    have h := hrect x hx (t 0) ht
    have heq : EuclideanSpace.single (0 : Fin 1) (t 0) = t := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp
    rwa [heq] at h
  have hslices := ae_memW12_coordinate_left_slice_of_memW12_ball hR hu hS U hrect'
  have hm := measurePreserving_domainOne_single.restrict_preimage hS
  have hpre : (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) ⁻¹' S = Ioo a b := by
    ext t
    simp only [S, mem_preimage, mem_setOf_eq, PiLp.single_apply, ↓reduceIte]
  rw [hpre] at hm
  exact (ae_restrict_iff' measurableSet_Ioo).mp (hm.quasiMeasurePreserving.ae hslices)

theorem result {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (U : OpenDomain n)
    {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ U.val, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ := (volume : Measure (Domain n)).restrict U.val
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp
          (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ᵐ c ∂volume, ∀ hc : c ∈ Ioo a b,
        ∃ hface : MemW12 U
          (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c)))
          (fun x i => Du (e.symm (x, EuclideanSpace.single (0 : Fin 1) c)) (Fin.castAdd 1 i)),
      ∃ L : C(Icc a c, Lp (Ambient q) 2 σ), ∃ R : C(Icc c b, Lp (Ambient q) 2 σ),
        (∀ t : Icc a c, L t = H ⟨t.val, t.property.1, t.property.2.trans hc.2.le⟩) ∧
        (∀ t : Icc c b, R t = H ⟨t.val, hc.1.le.trans t.property.1, t.property.2⟩) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
            L ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
          ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
            R ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        L ⟨c, hc.1.le, le_rfl⟩ = hface.2.1.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) ∧
        R ⟨c, le_rfl, hc.2.le⟩ = hface.2.1.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) ∧
        (∀ K : C(Icc a c, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
            ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = L) ∧
        ∀ K : C(Icc c b, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
            ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = R := by
  intro e σ
  obtain ⟨H, hH, hUnique⟩ := coordinate_ball_trace_existsUnique hR hu U hab hrect
  refine ⟨H, ⟨hH, ?_⟩, ?_⟩
  · have hcuts := continuous_lp_trace_cut_restrictions σ hab
      (f := fun p : Domain n × ℝ => u (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))) H hH
    have hfaces := ae_flat_sobolev_cut hR hu U hab hrect
    filter_upwards [hcuts, hfaces] with c hcutc hfacec
    intro hc
    let hface := hfacec hc
    obtain ⟨hcut, L, R, hLeq, hReq, hL, hR, hLend, hRend, hLU, hRU⟩ := hcutc hc
    have hclass : hcut.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) =
        hface.2.1.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) :=
      hcut.toLp_congr hface.2.1 (Filter.EventuallyEq.rfl)
    exact ⟨hface, L, R, hLeq, hReq, hL, hR, hLend.trans hclass, hRend.trans hclass, hLU, hRU⟩
  · intro K hK
    exact hUnique K hK.1

end StratificationTheory.Providers.CoordinateTraceJoint
