module

public import StratificationTheory.Foundation.CoordinateSliceConvergence
public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.SobolevL2Closure

/-!
# Actual Sobolev membership of complementary coordinate faces

A common smooth graph approximation retains the map and every fiber weak
column on almost every coordinate slice. The original ball data and rectangle
inclusion supply the finite fiber volume needed for weak-graph closure.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

private theorem finAddEquivProd_first_basis (m k : ℕ) (i : Fin m) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
      (EuclideanSpace.single (Fin.castAdd k i) (1 : ℝ)) =
        (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

private theorem coordinateDerivative_first_comp {m k q : ℕ}
    {f : Domain (m + k) → Ambient q} (hf : ContDiff ℝ ∞ f) (y : Domain k)
    (i : Fin m) (x : Domain m) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    let h := hf.comp (e.symm.contDiff.comp (contDiff_id.prodMk contDiff_const))
    coordinateDerivative (fun z : Domain m => f (e.symm (z, y))) h i x =
      coordinateDerivative f hf (Fin.castAdd k i) (e.symm (x, y)) := by
  intro e h
  have hp := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) y x)
  have he := e.symm.hasFDerivAt.comp x hp
  have hcomp := (hf.differentiable (by simp) (e.symm (x, y))).hasFDerivAt.comp x he
  change HasFDerivAt (fun z : Domain m => f (e.symm (z, y))) _ x at hcomp
  change fderiv ℝ (fun z : Domain m => f (e.symm (z, y))) x
    (EuclideanSpace.single i 1) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]
  change fderiv ℝ f (e.symm (x, y)) (e.symm (EuclideanSpace.single i 1, 0)) = _
  have hb : e.symm (EuclideanSpace.single i (1 : ℝ), 0) =
      EuclideanSpace.single (Fin.castAdd k i) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, finAddEquivProd_first_basis]
  rw [hb]
  rfl

/-- Almost every coordinate face of an actual finite Sobolev ball has finite
Sobolev membership on every contained open rectangular fiber. Its weak columns
are the original ambient columns with their actual coordinate indices. -/
theorem ae_memW12_coordinate_left_slice_of_memW12_ball {m k q : ℕ}
    {z : Domain (m + k)} {R : ℝ} (hR : 0 < R)
    {u : Domain (m + k) → Ambient q} {Du : Domain (m + k) → Gradient (m + k) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {S : Set (Domain k)} (hS : MeasurableSet S) (U : OpenDomain m)
    (hrect : ∀ x ∈ S, ∀ y ∈ U.val,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)).symm (y, x) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    ∀ᵐ x ∂volume.restrict S,
      MemW12 U (fun y => u (e.symm (y, x)))
        (fun y i => Du (e.symm (y, x)) (Fin.castAdd k i)) := by
  intro e
  by_cases hS0 : (volume : Measure (Domain k)) S = 0
  · rw [Measure.restrict_zero_set hS0]
    simp only [ae_zero, Filter.eventually_bot]
  let μ := (volume : Measure (Domain k)).restrict S
  let ν := (volume : Measure (Domain m)).restrict U.val
  let Ω := {y : Domain (m + k) | (e y).2 ∈ S ∧ (e y).1 ∈ U.val}
  have hΩ : MeasurableSet Ω :=
    (hS.preimage (continuous_snd.comp e.continuous).measurable).inter
      (U.property.measurableSet.preimage (continuous_fst.comp e.continuous).measurable)
  have hΩsub : Ω ⊆ ball z R := by
    intro y hy
    have h := hrect (e y).2 hy.1 (e y).1 hy.2
    rwa [e.symm_apply_apply] at h
  have hmeasure : (volume : Measure (Domain k)) S * (volume : Measure (Domain m)) U.val =
      (volume : Measure (Domain (m + k))) Ω := by
    have h := (Measure.measurePreserving_swap.comp
      (measurePreserving_finAddEquivProd m k)).measure_preimage
      (hS.prod U.property.measurableSet).nullMeasurableSet
    rw [Measure.prod_prod] at h
    exact h.symm
  have hprodFinite : (volume : Measure (Domain k)) S * (volume : Measure (Domain m)) U.val ≠ ⊤ := by
    rw [hmeasure]
    exact (lt_of_le_of_lt (measure_mono hΩsub) measure_ball_lt_top).ne
  have hUfinite : (volume : Measure (Domain m)) U.val ≠ ⊤ := by
    intro htop
    apply hprodFinite
    rw [htop, ENNReal.mul_top hS0]
  letI : IsFiniteMeasure (volume.restrict U.val) := isFiniteMeasure_restrict.mpr hUfinite
  have hraw := (measurePreserving_finAddEquivProd_symm m k).comp Measure.measurePreserving_swap
  have hm := hraw.restrict_preimage hΩ
  have hpre : (fun p : Domain k × Domain m => e.symm (p.2, p.1)) ⁻¹' Ω = S ×ˢ U.val := by
    ext p
    simp only [Ω, mem_preimage, mem_setOf_eq, e.apply_symm_apply, mem_prod]
  change MeasurePreserving (fun p : Domain k × Domain m => e.symm (p.2, p.1))
    ((volume.prod volume).restrict
      ((fun p : Domain k × Domain m => e.symm (p.2, p.1)) ⁻¹' Ω)) (volume.restrict Ω) at hm
  rw [hpre, ← Measure.prod_restrict] at hm
  have hμmono : volume.restrict Ω ≤ volume.restrict (ball z R) :=
    Measure.restrict_mono_set volume hΩsub
  obtain ⟨f, hf, hfW, hfConv, hfDConv⟩ := hu.smoothDensity_memW12_ball hR
  let F : Option (Fin m) → ℕ → Domain k × Domain m → Ambient q := fun j idx p =>
    match j with
    | none => f idx (e.symm (p.2, p.1))
    | some i => coordinateDerivative (f idx) (hf idx) (Fin.castAdd k i) (e.symm (p.2, p.1))
  let V : Option (Fin m) → Domain k × Domain m → Ambient q := fun j p =>
    match j with
    | none => u (e.symm (p.2, p.1))
    | some i => Du (e.symm (p.2, p.1)) (Fin.castAdd k i)
  have hF (j : Option (Fin m)) (idx : ℕ) : MemLp (F j idx) 2 (μ.prod ν) := by
    cases j with
    | none => exact ((hfW idx).2.1.mono_measure hμmono).comp_measurePreserving hm
    | some i => exact (((hfW idx).2.2 (Fin.castAdd k i)).mono_measure hμmono).comp_measurePreserving hm
  have hV (j : Option (Fin m)) : MemLp (V j) 2 (μ.prod ν) := by
    cases j with
    | none => exact (hu.2.1.mono_measure hμmono).comp_measurePreserving hm
    | some i => exact ((hu.2.2 (Fin.castAdd k i)).mono_measure hμmono).comp_measurePreserving hm
  have hConv (j : Option (Fin m)) : Tendsto (fun idx => eLpNorm (F j idx - V j) 2
      (μ.prod ν)) atTop (𝓝 0) := by
    let A : ℕ → Domain (m + k) → Ambient q := fun idx =>
      match j with
      | none => f idx - u
      | some i => fun y => coordinateDerivative (f idx) (hf idx) (Fin.castAdd k i) y - Du y (Fin.castAdd k i)
    have hA (idx : ℕ) : MemLp (A idx) 2 (volume.restrict (ball z R)) := by
      cases j with
      | none => exact (hfW idx).2.1.sub hu.2.1
      | some i => exact ((hfW idx).2.2 (Fin.castAdd k i)).sub (hu.2.2 (Fin.castAdd k i))
    have hlim : Tendsto (fun idx => eLpNorm (A idx) 2 (volume.restrict (ball z R)))
        atTop (𝓝 0) := by
      cases j with
      | none => exact hfConv
      | some i => exact hfDConv (Fin.castAdd k i)
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
  let fSlice : ℕ → Domain m → Ambient q := fun idx y => f (κ idx) (e.symm (y, x))
  let DfSlice : ℕ → Domain m → Gradient m q := fun idx y i =>
    coordinateDerivative (f (κ idx)) (hf (κ idx)) (Fin.castAdd k i) (e.symm (y, x))
  have hSmooth (idx : ℕ) : ContDiff ℝ ∞ (fSlice idx) :=
    (hf (κ idx)).comp (e.symm.contDiff.comp (contDiff_id.prodMk contDiff_const))
  have hDf (idx : ℕ) (i : Fin m) : coordinateDerivative (fSlice idx) (hSmooth idx) i =
      (fun y => DfSlice idx y i) := by
    funext y
    exact coordinateDerivative_first_comp (hf (κ idx)) x i y
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
