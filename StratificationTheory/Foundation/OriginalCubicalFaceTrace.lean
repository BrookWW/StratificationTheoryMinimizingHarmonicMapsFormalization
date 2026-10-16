module

public import StratificationTheory.Foundation.CoordinateACLQualification
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry
public import StratificationTheory.Foundation.NativeAffineFiberQualification
public import StratificationTheory.Foundation.RawBoundedLineTrace

/-!
# Original lower-face classes in higher-face native traces

Original Sobolev ball data with compact target values produce one
full-measure event of origins. On every subsequently chosen finite open
coordinate subface in a qualified line rectangle, the original lower-face
class is the cut of the original higher-face continuous native L2 trace.
No trace qualification or desired L2 limit is an input.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Original ball data produce actual higher-face traces through their
original lower-face classes, on one ambient full-measure event. The base
face may be chosen after its origin and only geometric carrier inclusion
and finite base measure are required of that choice. -/
theorem ae_original_cubical_face_raw_trace {n k q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q}
    {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {N : Set (Ambient q)} (hN : IsCompact N)
    (huN : ∀ᵐ y ∂volume.restrict (ball z R), u y ∈ N)
    (p : Equiv.Perm (Fin (n + 1)))
    (face : Fin k ↪ Fin (n + 1))
    (hface : ∀ j : Fin k, face j ≠ p (Fin.natAdd n (0 : Fin 1)))
    {S : Set (Domain n)} (hS : MeasurableSet S)
    {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := fun y : Domain (n + 1) => (e (Q.symm y)).1
    let B := fun t : Domain k =>
      ∑ l : Fin k, t l • EuclideanSpace.single (face l) (1 : ℝ)
    ∀ᵐ y ∂(volume : Measure (Domain (n + 1))),
      ∀ hy : y j ∈ Ioo a b, ∀ U : OpenDomain k,
      (volume : Measure (Domain k)) U.val ≠ ⊤ →
      (∀ s ∈ U.val, β (y + B s) ∈ S) →
      ∃ H : C(Icc (a - y j) (b - y j),
          Lp (Ambient q) 2 ((volume : Measure (Domain k)).restrict U.val)),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (a - y j) (b - y j),
          ∃ hslice : MemLp (fun s => u (y + B s + r • v)) 2 (volume.restrict U.val),
            H ⟨r, hr.1.le, hr.2.le⟩ =
              hslice.toLp (fun s => u (y + B s + r • v))) ∧
        (∃ hcut : MemLp (fun s => u (y + B s)) 2 (volume.restrict U.val),
          H ⟨0, sub_nonpos.mpr hy.1.le, sub_nonneg.mpr hy.2.le⟩ =
            hcut.toLp (fun s => u (y + B s))) ∧
        ∀ K : C(Icc (a - y j) (b - y j),
            Lp (Ambient q) 2 ((volume : Measure (Domain k)).restrict U.val)),
          (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (a - y j) (b - y j),
            ∃ hslice : MemLp (fun s => u (y + B s + r • v)) 2 (volume.restrict U.val),
              K ⟨r, hr.1.le, hr.2.le⟩ =
                hslice.toLp (fun s => u (y + B s + r • v))) → K = H := by
  intro Q e j v β B
  let Ω := {y : Domain (n + 1) | β y ∈ S ∧ (e (Q.symm y)).2 0 ∈ Ioo a b}
  let W := coordinatePermACLRepresentative p a b u Du
  let c := fun x t => Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
  let P : Domain (n + 1) → Prop := fun y => y ∈ Ω →
    W y = u y ∧
    MemLp (fun t => u (c (β y) t)) 2 (volume.restrict (Ioo a b)) ∧
    MemLp (fun t => Du (c (β y) t) j) 2 (volume.restrict (Ioo a b)) ∧
    AbsolutelyContinuousOnInterval (fun t => W (c (β y) t)) a b ∧
    (fun t => W (c (β y) t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => u (c (β y) t)) ∧
    (∀ t ∈ Icc a b, W (c (β y) t) ∈ N) ∧
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      W (c (β y) t) - W (c (β y) s) = ∫ r in s..t, Du (c (β y) r) j
  have hP : ∀ᵐ y ∂volume, P y := by
    have hACL := ae_coordinate_acl_closed_target_qualification
      hR hu hN.isClosed huN (fun _ : Unit => p) (fun _ => S) (fun _ => hS)
      (fun _ => a) (fun _ => b) (fun _ => hab) (fun _ => hrect)
    exact hACL.mono fun y hy => hy ()
  have hBm : Measurable B := by
    apply Continuous.measurable
    apply continuous_finsetSum
    intro l _
    exact (EuclideanSpace.proj l).continuous.smul continuous_const
  let shift : Domain k × ℝ → Domain (n + 1) := fun st => B st.1 + st.2 • v
  have hshift : Measurable shift :=
    (hBm.comp measurable_fst).add (measurable_snd.smul_const v)
  let u₀ := (ball z R).indicator u
  have hu₀ : AEStronglyMeasurable u₀ volume :=
    ((memLp_indicator_iff_restrict measurableSet_ball).mpr hu.2.1).aestronglyMeasurable
  have hlower := ae_native_translated_kernel_property volume B hBm hP
  have hupper := ae_native_translated_kernel_property (volume.prod volume) shift hshift hP
  have hmeas := ae_native_translated_kernel_aestronglyMeasurable
    (volume.prod volume) shift hshift hu₀
  obtain ⟨M, hM⟩ := hN.isBounded.exists_norm_le
  filter_upwards [hlower, hupper, hmeas] with y hyLower hyUpper hyMeas
  intro hy U hUfinite hbase
  let μ := (volume : Measure (Domain k)).restrict U.val
  let I := Ioo (a - y j) (b - y j)
  let ν := (volume : Measure ℝ).restrict I
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hUfinite
  let Y : Domain k × ℝ → Domain (n + 1) := fun st => y + B st.1 + st.2 • v
  let f : Domain k × ℝ → Ambient q := fun st => u (Y st)
  let F : Domain k × ℝ → Ambient q := fun st => W (Y st)
  have hshiftY (st : Domain k × ℝ) : y + shift st = Y st :=
    (add_assoc y (B st.1) (st.2 • v)).symm
  have hBj (s : Domain k) : B s j = 0 := by
    dsimp only [B]
    rw [coordinate_face_embedding_sum_eq_toLp]
    change (∑ l : Fin k, if face l = j then s l else 0) = 0
    have hnot (l : Fin k) : face l ≠ j := hface l
    simp only [hnot, ite_false, Finset.sum_const_zero]
  have hbasej (s : Domain k) : (y + B s) j = y j := by
    change y j + B s j = y j
    rw [hBj, add_zero]
  have hbaseΩ (s : Domain k) (hs : s ∈ U.val) : y + B s ∈ Ω := by
    refine ⟨hbase s hs, ?_⟩
    rw [coordinate_split_last_eq, hbasej]
    exact hy
  have hYΩ (s : Domain k) (hs : s ∈ U.val) (r : ℝ) (hr : r ∈ I) : Y (s, r) ∈ Ω := by
    have hcoords := coordinate_normal_translation_coordinates p (y + B s) r
    change β (Y (s, r)) = β (y + B s) ∧
      (e (Q.symm (Y (s, r)))).2 0 = (y + B s) j + r at hcoords
    refine ⟨hcoords.1 ▸ hbase s hs, ?_⟩
    rw [hcoords.2, hbasej]
    exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hΩball (x : Domain (n + 1)) (hx : x ∈ Ω) : x ∈ ball z R := by
    have h := hrect (β x) hx.1 ((e (Q.symm x)).2 0) hx.2
    rw [cylinder_coordinates_inverse_left n (Q.symm x), Q.apply_symm_apply] at h
    exact h
  have hmem : ∀ᵐ st ∂μ.prod ν, st.1 ∈ U.val ∧ st.2 ∈ I := by
    exact ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae
      (ae_restrict_mem U.property.measurableSet)).and
      ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae
        (ae_restrict_mem measurableSet_Ioo))
  have hprodle : μ.prod ν ≤ (volume : Measure (Domain k)).prod (volume : Measure ℝ) :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hYraw : (fun st => u₀ (Y st)) =ᵐ[μ.prod ν] f := by
    filter_upwards [hmem] with st hst
    exact Set.indicator_of_mem (hΩball _ (hYΩ st.1 hst.1 st.2 hst.2)) u
  have hfmeas : AEStronglyMeasurable f (μ.prod ν) := by
    have hm := hyMeas.mono_measure hprodle
    have hm' : AEStronglyMeasurable (fun st => u₀ (Y st)) (μ.prod ν) :=
      hm.congr (Eventually.of_forall fun st => congrArg u₀ (hshiftY st))
    exact hm'.congr hYraw
  have hFraw : F =ᵐ[μ.prod ν] f := by
    have hupper := hyUpper.filter_mono (ae_mono hprodle)
    filter_upwards [hupper, hmem] with st hst hmemst
    have hst' : P (Y st) := hshiftY st ▸ hst
    exact (hst' (hYΩ st.1 hmemst.1 st.2 hmemst.2)).1
  have hfmeasTime : ∀ᵐ r : ℝ ∂volume, ∀ _hr : r ∈ I,
      AEStronglyMeasurable (fun s => f (s, r)) μ :=
    (ae_restrict_iff' measurableSet_Ioo).mp hfmeas.prodMk_right
  have hFrawTime : ∀ᵐ r : ℝ ∂volume, ∀ _hr : r ∈ I,
      (fun s => F (s, r)) =ᵐ[μ] (fun s => f (s, r)) := by
    have h := Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hFraw)
    exact (ae_restrict_iff' measurableSet_Ioo).mp h
  have hline (s : Domain k) (r : ℝ) : c (β (y + B s)) (y j + r) = Y (s, r) := by
    have h := coordinate_line_eq_add_normal p (y + B s) (y j + r)
    change c (β (y + B s)) (y j + r) = (y + B s) + (y j + r - (y + B s) j) • v at h
    simpa only [hbasej, add_sub_cancel_left] using h
  have htime (r : ℝ) (hr : r ∈ Icc (a - y j) (b - y j)) : y j + r ∈ Icc a b :=
    ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hcont : ∀ᵐ s ∂μ, ContinuousOn (fun r => F (s, r)) (Icc (a - y j) (b - y j)) := by
    filter_upwards [ae_restrict_of_ae hyLower, ae_restrict_mem U.property.measurableSet] with s hs hsU
    obtain ⟨_hraw, _hLp, _hD, hAC, _hAE, _hvalues, _hinc⟩ := hs (hbaseΩ s hsU)
    have hc₀ : ContinuousOn (fun t => W (c (β (y + B s)) t)) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hAC.continuousOn
    have hc := hc₀.comp
      (show ContinuousOn (fun r : ℝ => y j + r) (Icc (a - y j) (b - y j)) from
        (continuous_const.add continuous_id).continuousOn) htime
    apply hc.congr
    intro r _hr
    exact congrArg W (hline s r).symm
  have hbound : ∀ᵐ s ∂μ, ∀ r ∈ Icc (a - y j) (b - y j), ‖F (s, r)‖ ≤ M := by
    filter_upwards [ae_restrict_of_ae hyLower, ae_restrict_mem U.property.measurableSet] with s hs hsU
    obtain ⟨_hraw, _hLp, _hD, _hAC, _hAE, hvalues, _hinc⟩ := hs (hbaseΩ s hsU)
    intro r hr
    have hvN := hvalues (y j + r) (htime r hr)
    rw [hline] at hvN
    exact hM _ hvN
  have hcut : (fun s => F (s, 0)) =ᵐ[μ] (fun s => f (s, 0)) := by
    filter_upwards [ae_restrict_of_ae hyLower, ae_restrict_mem U.property.measurableSet] with s hs hsU
    simpa only [F, f, Y, zero_smul, add_zero] using (hs (hbaseΩ s hsU)).1
  have hab' : a - y j < b - y j := sub_lt_sub_right hab _
  obtain ⟨H, hHraw, hHcut, hHunique⟩ := exists_raw_L2_trace_of_bounded_line_data
    μ hab' hfmeasTime hFrawTime hcont hbound
      ⟨0, sub_nonpos.mpr hy.1.le, sub_nonneg.mpr hy.2.le⟩ hcut
  refine ⟨H, hHraw, ?_, hHunique⟩
  simpa only [f, Y, zero_smul, add_zero] using hHcut

/-- Every dimension and every incident normal of a countable prescribed
coordinate-face family shares one original full-measure qualification
event. All original raw subface classes are retained by their actual native
continuous traces, on every subsequently chosen finite contained patch. -/
theorem ae_original_cubical_face_family_raw_trace
    {n q : ℕ} {ι : Type*} [Countable ι]
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q}
    {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {N : Set (Ambient q)} (hN : IsCompact N)
    (huN : ∀ᵐ y ∂volume.restrict (ball z R), u y ∈ N)
    (k : ι → ℕ) (p : ι → Equiv.Perm (Fin (n + 1)))
    (face : ∀ i, Fin (k i) ↪ Fin (n + 1))
    (hface : ∀ (i : ι) (l : Fin (k i)), face i l ≠ p i (Fin.natAdd n (0 : Fin 1)))
    (S : ι → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := fun i => p i (Fin.natAdd n (0 : Fin 1))
    let v := fun i => EuclideanSpace.single (j i) (1 : ℝ)
    let β := fun i (y : Domain (n + 1)) => (e ((Q i).symm y)).1
    let B := fun i (t : Domain (k i)) =>
      ∑ l : Fin (k i), t l • EuclideanSpace.single (face i l) (1 : ℝ)
    ∀ᵐ y ∂(volume : Measure (Domain (n + 1))), ∀ i,
      ∀ hy : y (j i) ∈ Ioo (a i) (b i), ∀ U : OpenDomain (k i),
      (volume : Measure (Domain (k i))) U.val ≠ ⊤ →
      (∀ s ∈ U.val, β i (y + B i s) ∈ S i) →
      ∃ H : C(Icc (a i - y (j i)) (b i - y (j i)),
          Lp (Ambient q) 2 ((volume : Measure (Domain (k i))).restrict U.val)),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (a i - y (j i)) (b i - y (j i)),
          ∃ hslice : MemLp (fun s => u (y + B i s + r • v i)) 2 (volume.restrict U.val),
            H ⟨r, hr.1.le, hr.2.le⟩ =
              hslice.toLp (fun s => u (y + B i s + r • v i))) ∧
        (∃ hcut : MemLp (fun s => u (y + B i s)) 2 (volume.restrict U.val),
          H ⟨0, sub_nonpos.mpr hy.1.le, sub_nonneg.mpr hy.2.le⟩ =
            hcut.toLp (fun s => u (y + B i s))) ∧
        ∀ K : C(Icc (a i - y (j i)) (b i - y (j i)),
            Lp (Ambient q) 2 ((volume : Measure (Domain (k i))).restrict U.val)),
          (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (a i - y (j i)) (b i - y (j i)),
            ∃ hslice : MemLp (fun s => u (y + B i s + r • v i)) 2 (volume.restrict U.val),
              K ⟨r, hr.1.le, hr.2.le⟩ =
                hslice.toLp (fun s => u (y + B i s + r • v i))) → K = H := by
  intro Q e j v β B
  exact ae_all_iff.mpr fun i => ae_original_cubical_face_raw_trace
    hR hu hN huN (p i) (face i) (hface i) (hS i) (hab i) (hrect i)

end StratificationTheory
