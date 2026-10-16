module

public import StratificationTheory.Foundation.CoordinateFaceQualification
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Complete original weak graphs on ball fibers

Almost every coordinate plane inherits the original finite Sobolev pair on
its entire open intersection with the ball. The fiber domain depends on the
base point; no prescribed rectangular subdomain is required.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

private theorem coordinate_split_fiber_basis (m k : ℕ) (i : Fin k) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
      (EuclideanSpace.single (Fin.natAdd m i) (1 : ℝ)) =
        (0, EuclideanSpace.single i 1) := by
  apply Prod.ext
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

private theorem coordinate_derivative_split_fiber {m k q : ℕ}
    {f : Domain (m + k) → Ambient q} (hf : ContDiff ℝ ∞ f) (x : Domain m)
    (i : Fin k) (y : Domain k) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    let h := hf.comp (e.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))
    coordinateDerivative (fun t : Domain k => f (e.symm (x, t))) h i y =
      coordinateDerivative f hf (Fin.natAdd m i) (e.symm (x, y)) := by
  intro e h
  have hp := (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have he := e.symm.hasFDerivAt.comp y hp
  have hcomp := (hf.differentiable (by simp) (e.symm (x, y))).hasFDerivAt.comp y he
  change HasFDerivAt (fun t : Domain k => f (e.symm (x, t))) _ y at hcomp
  change fderiv ℝ (fun t : Domain k => f (e.symm (x, t))) y
    (EuclideanSpace.single i 1) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]
  change fderiv ℝ f (e.symm (x, y)) (e.symm (0, EuclideanSpace.single i 1)) = _
  have hb : e.symm (0, EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single (Fin.natAdd m i) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, coordinate_split_fiber_basis]
  rw [hb]
  rfl

/-- Almost every coordinate plane has the complete original finite weak graph
on its whole open intersection with the original ball. In particular, any
open face subsequently selected inside that fiber may be restricted from
this same original pair. -/
theorem ae_memW12_ball_coordinate_fiber {m k q : ℕ}
    {z : Domain (m + k)} {R : ℝ} (hR : 0 < R)
    {u : Domain (m + k) → Ambient q}
    {Du : Domain (m + k) → Gradient (m + k) q}
    (hu : MemW12 (ballDomain z R) u Du) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    ∀ᵐ x ∂(volume : Measure (Domain m)),
      MemW12
        ⟨(fun y : Domain k => e.symm (x, y)) ⁻¹' ball z R,
          isOpen_ball.preimage (e.symm.continuous.comp
            (continuous_const.prodMk continuous_id))⟩
        (fun y => u (e.symm (x, y)))
        (fun y i => Du (e.symm (x, y)) (Fin.natAdd m i)) := by
  intro e
  let Ω := e.symm ⁻¹' ball z R
  have hΩ : MeasurableSet Ω := measurableSet_ball.preimage e.symm.continuous.measurable
  have hm := measurePreserving_finAddEquivProd_symm m k
  obtain ⟨f, hf, hfW, hfConv, hfDConv⟩ := hu.smoothDensity_memW12_ball hR
  let A : Option (Fin k) → ℕ → Domain (m + k) → Ambient q := fun j idx =>
    match j with
    | none => f idx
    | some i => coordinateDerivative (f idx) (hf idx) (Fin.natAdd m i)
  let B : Option (Fin k) → Domain (m + k) → Ambient q := fun j =>
    match j with
    | none => u
    | some i => fun y => Du y (Fin.natAdd m i)
  let F : Option (Fin k) → ℕ → Domain m × Domain k → Ambient q := fun j idx =>
    Ω.indicator (fun p => A j idx (e.symm p))
  let V : Option (Fin k) → Domain m × Domain k → Ambient q := fun j =>
    Ω.indicator (fun p => B j (e.symm p))
  have hA (j : Option (Fin k)) (idx : ℕ) :
      MemLp (A j idx) 2 (volume.restrict (ball z R)) := by
    cases j with
    | none => exact (hfW idx).2.1
    | some i => exact (hfW idx).2.2 (Fin.natAdd m i)
  have hB (j : Option (Fin k)) : MemLp (B j) 2 (volume.restrict (ball z R)) := by
    cases j with
    | none => exact hu.2.1
    | some i => exact hu.2.2 (Fin.natAdd m i)
  have hF (j : Option (Fin k)) (idx : ℕ) : MemLp (F j idx) 2 (volume.prod volume) := by
    apply (memLp_indicator_iff_restrict hΩ).mpr
    exact (hA j idx).comp_measurePreserving (hm.restrict_preimage measurableSet_ball)
  have hV (j : Option (Fin k)) : MemLp (V j) 2 (volume.prod volume) := by
    apply (memLp_indicator_iff_restrict hΩ).mpr
    exact (hB j).comp_measurePreserving (hm.restrict_preimage measurableSet_ball)
  have hConv (j : Option (Fin k)) : Tendsto (fun idx => eLpNorm (F j idx - V j) 2
      (volume.prod volume)) atTop (𝓝 0) := by
    have heq (idx : ℕ) : eLpNorm (F j idx - V j) 2 (volume.prod volume) =
        eLpNorm (A j idx - B j) 2 (volume.restrict (ball z R)) := by
      change eLpNorm (fun p => Ω.indicator (fun p => A j idx (e.symm p)) p -
        Ω.indicator (fun p => B j (e.symm p)) p) 2 (volume.prod volume) = _
      rw [← Set.indicator_sub, eLpNorm_indicator_eq_eLpNorm_restrict hΩ]
      exact eLpNorm_comp_measurePreserving
        (((hA j idx).sub (hB j)).aestronglyMeasurable)
        (hm.restrict_preimage measurableSet_ball)
    simp_rw [heq]
    cases j with
    | none => exact hfConv
    | some i => exact hfDConv (Fin.natAdd m i)
  obtain ⟨κ, _hκ, hae⟩ := exists_subseq_ae_tendsto_prod_l2_family hF hV hConv
  filter_upwards [hae] with x hx
  let U : OpenDomain k :=
    ⟨(fun y : Domain k => e.symm (x, y)) ⁻¹' ball z R,
      isOpen_ball.preimage (e.symm.continuous.comp (continuous_const.prodMk continuous_id))⟩
  have hU : MeasurableSet U.val := U.property.measurableSet
  have hUfinite : (volume : Measure (Domain k)) U.val ≠ ⊤ := by
    let L : Domain (m + k) →L[ℝ] Domain k :=
      (ContinuousLinearMap.snd ℝ (Domain m) (Domain k)).comp e.toContinuousLinearMap
    have hb := L.lipschitz.isBounded_image (isBounded_ball (x := z) (r := R))
    apply (hb.subset ?_).measure_lt_top.ne
    intro y hy
    refine ⟨e.symm (x, y), hy, ?_⟩
    change (e (e.symm (x, y))).2 = y
    rw [e.apply_symm_apply]
  letI : IsFiniteMeasure (volume.restrict U.val) := isFiniteMeasure_restrict.mpr hUfinite
  have hFlp (j : Option (Fin k)) (idx : ℕ) :
      MemLp (fun y => A j idx (e.symm (x, y))) 2 (volume.restrict U.val) := by
    apply (memLp_indicator_iff_restrict hU).mp
    exact (hx j).1 idx
  have hVlp (j : Option (Fin k)) :
      MemLp (fun y => B j (e.symm (x, y))) 2 (volume.restrict U.val) := by
    apply (memLp_indicator_iff_restrict hU).mp
    exact (hx j).2.1
  have hSliceConv (j : Option (Fin k)) : Tendsto (fun idx => eLpNorm
      (fun y => A j (κ idx) (e.symm (x, y)) - B j (e.symm (x, y)))
        2 (volume.restrict U.val)) atTop (𝓝 0) := by
    have heq (idx : ℕ) :
        eLpNorm (fun y => F j (κ idx) (x, y) - V j (x, y)) 2 volume =
        eLpNorm (fun y => A j (κ idx) (e.symm (x, y)) - B j (e.symm (x, y)))
          2 (volume.restrict U.val) := by
      change eLpNorm (fun y => U.val.indicator (fun y => A j (κ idx) (e.symm (x, y))) y -
        U.val.indicator (fun y => B j (e.symm (x, y))) y) 2 volume = _
      rw [← Set.indicator_sub, eLpNorm_indicator_eq_eLpNorm_restrict hU]
    exact ((hx j).2.2).congr fun idx => heq idx
  let fSlice : ℕ → Domain k → Ambient q := fun idx y => f (κ idx) (e.symm (x, y))
  let DfSlice : ℕ → Domain k → Gradient k q := fun idx y i =>
    coordinateDerivative (f (κ idx)) (hf (κ idx)) (Fin.natAdd m i) (e.symm (x, y))
  have hSmooth (idx : ℕ) : ContDiff ℝ ∞ (fSlice idx) :=
    (hf (κ idx)).comp (e.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))
  have hDf (idx : ℕ) (i : Fin k) : coordinateDerivative (fSlice idx) (hSmooth idx) i =
      (fun y => DfSlice idx y i) := by
    funext y
    exact coordinate_derivative_split_fiber (hf (κ idx)) x i y
  have hSliceW (idx : ℕ) : MemW12 U (fSlice idx) (DfSlice idx) := by
    have h := memW12_of_contDiff U (hSmooth idx) (hFlp none (κ idx))
      (fun i => by rw [hDf]; exact hFlp (some i) (κ idx))
    have heq : (fun y i => coordinateDerivative (fSlice idx) (hSmooth idx) i y) =
        DfSlice idx := by
      funext y i
      exact congrFun (hDf idx i) y
    rwa [heq] at h
  exact MemW12.of_L2_limit hSliceW (hVlp none) (fun i => hVlp (some i))
    (hSliceConv none) (fun i => hSliceConv (some i))

/-- A countable family of arbitrary coordinate dimensions has one ambient
full-measure event on which every subsequently chosen open face inside the
original ball retains the original map and all corresponding original weak
columns. The open face may depend on the eventual grid offset. -/
theorem ae_memW12_all_coordinate_faces_of_memW12_ball
    {N q : ℕ} {ι : Type*} [Countable ι]
    {z : Domain N} {R : ℝ} (hR : 0 < R)
    {u : Domain N → Ambient q} {Du : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z R) u Du)
    (m k : ι → ℕ) (p : ∀ i, Fin (m i + k i) ≃ Fin N) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)
    let F := fun i (y : Domain N) (t : Domain (k i)) =>
      Q i ((e i).symm ((e i ((Q i).symm y)).1, t))
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ (i : ι) (U : OpenDomain (k i)),
      (∀ t ∈ U.val, F i y t ∈ ball z R) →
      MemW12 U (fun t => u (F i y t))
        (fun t j => Du (F i y t) (p i (Fin.natAdd (m i) j))) := by
  intro Q e F
  apply ae_all_iff.mpr
  intro i
  have huQ := memW12_ball_coordinateEquiv hR hu (p i)
  have hbase := ae_memW12_ball_coordinate_fiber hR huQ
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Domain (m i))))
    (ν := (volume : Measure (Domain (k i))))).ae hbase
  have hambient := ((measurePreserving_finAddEquivProd (m i) (k i)).comp
    (Q i).symm.measurePreserving).quasiMeasurePreserving.ae hprod
  filter_upwards [hambient] with y hy
  intro U hU
  let V : OpenDomain (k i) :=
    ⟨(fun t : Domain (k i) => (e i).symm ((e i ((Q i).symm y)).1, t)) ⁻¹'
      ball ((Q i).symm z) R,
      isOpen_ball.preimage ((e i).symm.continuous.comp
        (continuous_const.prodMk continuous_id))⟩
  have hV : MemW12 V (fun t => u (F i y t))
      (fun t j => Du (F i y t) (p i (Fin.natAdd (m i) j))) := hy
  have hsub : U.val ⊆ V.val := by
    intro t ht
    change (e i).symm ((e i ((Q i).symm y)).1, t) ∈ ball ((Q i).symm z) R
    rw [← (Q i).preimage_ball]
    exact hU t ht
  exact ⟨hV.1.mono hsub,
    hV.2.1.mono_measure (Measure.restrict_mono_set volume hsub),
    fun j => (hV.2.2 j).mono_measure (Measure.restrict_mono_set volume hsub)⟩

end StratificationTheory
