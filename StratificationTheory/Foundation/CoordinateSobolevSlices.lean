module

public import StratificationTheory.Foundation.CoordinateSliceConvergence
public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.SobolevL2Closure

/-!
# Actual Sobolev membership of coordinate faces

A common smooth graph approximation retains the map and every fiber weak
column on almost every coordinate slice. The original ball data and rectangle
inclusion supply the finite fiber volume needed for weak-graph closure.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

private theorem finAddEquivProd_fiber_basis (m k : ℕ) (i : Fin k) :
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

private theorem coordinateDerivative_fiber_comp {m k q : ℕ}
    {f : Domain (m + k) → Ambient q} (hf : ContDiff ℝ ∞ f) (x : Domain m)
    (i : Fin k) (y : Domain k) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    let h := hf.comp (e.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))
    coordinateDerivative (fun z : Domain k => f (e.symm (x, z))) h i y =
      coordinateDerivative f hf (Fin.natAdd m i) (e.symm (x, y)) := by
  intro e h
  have hp := (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have he := e.symm.hasFDerivAt.comp y hp
  have hcomp := (hf.differentiable (by simp) (e.symm (x, y))).hasFDerivAt.comp y he
  change HasFDerivAt (fun z : Domain k => f (e.symm (x, z))) _ y at hcomp
  change fderiv ℝ (fun z : Domain k => f (e.symm (x, z))) y
    (EuclideanSpace.single i 1) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]
  change fderiv ℝ f (e.symm (x, y)) (e.symm (0, EuclideanSpace.single i 1)) = _
  have hb : e.symm (0, EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single (Fin.natAdd m i) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, finAddEquivProd_fiber_basis]
  rw [hb]
  rfl

/-- Almost every coordinate face of an actual finite Sobolev ball has finite
Sobolev membership on every contained open rectangular fiber. Its weak columns
are the original ambient columns with their actual coordinate indices. -/
theorem ae_memW12_coordinate_slice_of_memW12_ball {m k q : ℕ}
    {z : Domain (m + k)} {R : ℝ} (hR : 0 < R)
    {u : Domain (m + k) → Ambient q} {Du : Domain (m + k) → Gradient (m + k) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {S : Set (Domain m)} (hS : MeasurableSet S) (U : OpenDomain k)
    (hrect : ∀ x ∈ S, ∀ y ∈ U.val,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)).symm (x, y) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    ∀ᵐ x ∂volume.restrict S,
      MemW12 U (fun y => u (e.symm (x, y)))
        (fun y i => Du (e.symm (x, y)) (Fin.natAdd m i)) := by
  intro e
  by_cases hS0 : (volume : Measure (Domain m)) S = 0
  · rw [Measure.restrict_zero_set hS0]
    simp only [ae_zero, Filter.eventually_bot]
  let μ := (volume : Measure (Domain m)).restrict S
  let ν := (volume : Measure (Domain k)).restrict U.val
  let Ω := {y : Domain (m + k) | (e y).1 ∈ S ∧ (e y).2 ∈ U.val}
  have hΩ : MeasurableSet Ω :=
    (hS.preimage (continuous_fst.comp e.continuous).measurable).inter
      (U.property.measurableSet.preimage (continuous_snd.comp e.continuous).measurable)
  have hΩsub : Ω ⊆ ball z R := by
    intro y hy
    have h := hrect (e y).1 hy.1 (e y).2 hy.2
    rwa [e.symm_apply_apply] at h
  have hmeasure : (volume : Measure (Domain m)) S * (volume : Measure (Domain k)) U.val =
      (volume : Measure (Domain (m + k))) Ω := by
    have h := (measurePreserving_finAddEquivProd m k).measure_preimage
      (hS.prod U.property.measurableSet).nullMeasurableSet
    rw [Measure.prod_prod] at h
    exact h.symm
  have hprodFinite : (volume : Measure (Domain m)) S * (volume : Measure (Domain k)) U.val ≠ ⊤ := by
    rw [hmeasure]
    exact (lt_of_le_of_lt (measure_mono hΩsub) measure_ball_lt_top).ne
  have hUfinite : (volume : Measure (Domain k)) U.val ≠ ⊤ := by
    intro htop
    apply hprodFinite
    rw [htop, ENNReal.mul_top hS0]
  letI : IsFiniteMeasure (volume.restrict U.val) := isFiniteMeasure_restrict.mpr hUfinite
  have hm := (measurePreserving_finAddEquivProd_symm m k).restrict_preimage hΩ
  have hpre : e.symm ⁻¹' Ω = S ×ˢ U.val := by
    ext p
    simp only [Ω, mem_preimage, mem_setOf_eq, e.apply_symm_apply, mem_prod]
  rw [hpre, ← Measure.prod_restrict] at hm
  have hμmono : volume.restrict Ω ≤ volume.restrict (ball z R) :=
    Measure.restrict_mono_set volume hΩsub
  obtain ⟨f, hf, hfW, hfConv, hfDConv⟩ := hu.smoothDensity_memW12_ball hR
  let F : Option (Fin k) → ℕ → Domain m × Domain k → Ambient q := fun j idx p =>
    match j with
    | none => f idx (e.symm p)
    | some i => coordinateDerivative (f idx) (hf idx) (Fin.natAdd m i) (e.symm p)
  let V : Option (Fin k) → Domain m × Domain k → Ambient q := fun j p =>
    match j with
    | none => u (e.symm p)
    | some i => Du (e.symm p) (Fin.natAdd m i)
  have hF (j : Option (Fin k)) (idx : ℕ) : MemLp (F j idx) 2 (μ.prod ν) := by
    cases j with
    | none => exact ((hfW idx).2.1.mono_measure hμmono).comp_measurePreserving hm
    | some i => exact (((hfW idx).2.2 (Fin.natAdd m i)).mono_measure hμmono).comp_measurePreserving hm
  have hV (j : Option (Fin k)) : MemLp (V j) 2 (μ.prod ν) := by
    cases j with
    | none => exact (hu.2.1.mono_measure hμmono).comp_measurePreserving hm
    | some i => exact ((hu.2.2 (Fin.natAdd m i)).mono_measure hμmono).comp_measurePreserving hm
  have hConv (j : Option (Fin k)) : Tendsto (fun idx => eLpNorm (F j idx - V j) 2
      (μ.prod ν)) atTop (𝓝 0) := by
    let A : ℕ → Domain (m + k) → Ambient q := fun idx =>
      match j with
      | none => f idx - u
      | some i => fun y => coordinateDerivative (f idx) (hf idx) (Fin.natAdd m i) y - Du y (Fin.natAdd m i)
    have hA (idx : ℕ) : MemLp (A idx) 2 (volume.restrict (ball z R)) := by
      cases j with
      | none => exact (hfW idx).2.1.sub hu.2.1
      | some i => exact ((hfW idx).2.2 (Fin.natAdd m i)).sub (hu.2.2 (Fin.natAdd m i))
    have hlim : Tendsto (fun idx => eLpNorm (A idx) 2 (volume.restrict (ball z R)))
        atTop (𝓝 0) := by
      cases j with
      | none => exact hfConv
      | some i => exact hfDConv (Fin.natAdd m i)
    have heq (idx : ℕ) : eLpNorm (F j idx - V j) 2 (μ.prod ν) =
        eLpNorm (A idx) 2 (volume.restrict Ω) := by
      have hh := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
        ((hA idx).mono_measure hμmono).aestronglyMeasurable hm
      cases j <;> exact hh
    simp_rw [heq]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun idx => eLpNorm_mono_measure (A idx) hμmono)
  obtain ⟨κ, _hκ, hae⟩ := exists_subseq_ae_tendsto_prod_l2_family hF hV hConv
  filter_upwards [hae] with x hx
  let fSlice : ℕ → Domain k → Ambient q := fun idx y => f (κ idx) (e.symm (x, y))
  let DfSlice : ℕ → Domain k → Gradient k q := fun idx y i =>
    coordinateDerivative (f (κ idx)) (hf (κ idx)) (Fin.natAdd m i) (e.symm (x, y))
  have hSmooth (idx : ℕ) : ContDiff ℝ ∞ (fSlice idx) :=
    (hf (κ idx)).comp (e.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))
  have hDf (idx : ℕ) (i : Fin k) : coordinateDerivative (fSlice idx) (hSmooth idx) i =
      (fun y => DfSlice idx y i) := by
    funext y
    exact coordinateDerivative_fiber_comp (hf (κ idx)) x i y
  have hSliceW (idx : ℕ) : MemW12 U (fSlice idx) (DfSlice idx) := by
    have h := memW12_of_contDiff U (hSmooth idx) ((hx none).1 (κ idx))
      (fun i => by rw [hDf]; exact (hx (some i)).1 (κ idx))
    have hh : (fun y i => coordinateDerivative (fSlice idx) (hSmooth idx) i y) = DfSlice idx := by
      funext y i
      exact congrFun (hDf idx i) y
    rwa [hh] at h
  exact MemW12.of_L2_limit hSliceW (hx none).2.1 (fun i => (hx (some i)).2.1)
    (hx none).2.2 (fun i => (hx (some i)).2.2)

end StratificationTheory
