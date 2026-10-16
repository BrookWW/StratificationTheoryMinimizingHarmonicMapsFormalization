module

public import StratificationTheory.Foundation.DominatedL2Pullback
public import StratificationTheory.Foundation.RadialSobolevPullback
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.SobolevL2Closure
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Actual smooth domain pullback of finite Sobolev graphs

Smooth coordinates with bounded differential and finite native pushforward
distortion preserve the full original weak graph. The displayed weak columns
are the chain rule applied to the original columns, proved by simultaneous
smooth graph approximation on the source ball.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators
namespace StratificationTheory

private theorem smooth_fderiv_apply_sum {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) (x v : Domain n) :
    fderiv ℝ f x v = ∑ j : Fin n, v j • coordinateDerivative f hf j x := by
  have hv : (∑ j : Fin n, v j • EuclideanSpace.single j 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    fderiv ℝ f x v = fderiv ℝ f x (∑ j : Fin n, v j • EuclideanSpace.single j 1) :=
      congrArg (fderiv ℝ f x) hv.symm
    _ = _ := by simp only [map_sum, map_smul, coordinateDerivative]

private theorem smooth_coordinate_pullback_fderiv {m n q : ℕ}
    (U : OpenDomain m) {F : Domain m → Domain n} (hF : ContDiffOn ℝ ∞ F U.val)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f)
    {x : Domain m} (hx : x ∈ U.val) (i : Fin m) :
    fderiv ℝ (f ∘ F) x (EuclideanSpace.single i 1) =
      ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j •
        coordinateDerivative f hf j (F x) := by
  have hFd : DifferentiableAt ℝ F x :=
    (hF.differentiableOn (by simp)).differentiableAt (U.property.mem_nhds hx)
  have hfd : DifferentiableAt ℝ f (F x) := hf.differentiable (by simp) (F x)
  rw [(hfd.hasFDerivAt.comp x hFd.hasFDerivAt).fderiv]
  exact smooth_fderiv_apply_sum hf (F x) (fderiv ℝ F x (EuclideanSpace.single i 1))

private theorem smooth_domain_coefficient_memLp_top {m n : ℕ}
    (U : OpenDomain m) (F : Domain m → Domain n) (hF : ContDiffOn ℝ ∞ F U.val)
    (L : ℝ) (hDF : ∀ x ∈ U.val, ‖fderiv ℝ F x‖ ≤ L) (i : Fin m) (j : Fin n) :
    MemLp (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j) ∞
      (volume.restrict U.val) := by
  have hcont : ContinuousOn (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j)
      U.val :=
    (EuclideanSpace.proj j).continuous.continuousOn.comp
      ((hF.continuousOn_fderiv_of_isOpen U.property (by simp)).clm_apply
        continuousOn_const) (mapsTo_univ _ _)
  apply memLp_top_of_bound (hcont.aestronglyMeasurable U.property.measurableSet) L
  filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
  calc
    ‖(fderiv ℝ F x (EuclideanSpace.single i 1)) j‖ ≤
        ‖fderiv ℝ F x (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ j
    _ ≤ ‖fderiv ℝ F x‖ * ‖EuclideanSpace.single i 1‖ :=
      (fderiv ℝ F x).le_opNorm _
    _ = ‖fderiv ℝ F x‖ := by
      have he : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
        simpa only [norm_one] using PiLp.norm_single 2 (fun _ : Fin m => ℝ) i (1 : ℝ)
      rw [he, mul_one]
    _ ≤ L := hDF x hx

private theorem hasWeakGradient_smooth_coordinate_pullback {m n q : ℕ}
    (U : OpenDomain m) {F : Domain m → Domain n} (hF : ContDiffOn ℝ ∞ F U.val)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) :
    HasWeakGradient U (f ∘ F)
      (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j •
        coordinateDerivative f hf j (F x)) := by
  have hweak := hasWeakGradient_of_contDiffOn U (hf.comp_contDiffOn hF)
  apply hweak.congr_ae EventuallyEq.rfl
  filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
  funext i
  exact smooth_coordinate_pullback_fderiv U hF hf hx i

/-- A smooth coordinate map with bounded differential and actual finite native
measure distortion pulls back the original Sobolev pair. No weak chain rule
or transformed Sobolev membership is an input. -/
theorem memW12_smooth_domain_pullback_ball {m n q : ℕ}
    {z : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain z R) u Du)
    (U : OpenDomain m) (hfinite : (volume : Measure (Domain m)) U.val ≠ ⊤)
    (F : Domain m → Domain n) (hF : ContDiffOn ℝ ∞ F U.val)
    (L : ℝ) (hDF : ∀ x ∈ U.val, ‖fderiv ℝ F x‖ ≤ L)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hmap : Measure.map F (volume.restrict U.val) ≤
      c • volume.restrict (ball z R)) :
    MemW12 U (u ∘ F)
      (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j •
        Du (F x) j) := by
  let μ : Measure (Domain m) := volume.restrict U.val
  let ν : Measure (Domain n) := volume.restrict (ball z R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinite
  have hFm : AEMeasurable F μ := hF.continuousOn.aemeasurable U.property.measurableSet
  let a : Fin m → Fin n → Domain m → ℝ := fun i j x =>
    (fderiv ℝ F x (EuclideanSpace.single i 1)) j
  have ha (i : Fin m) (j : Fin n) : MemLp (a i j) ∞ μ :=
    smooth_domain_coefficient_memLp_top U F hF L hDF i j
  have hcomp {f : Domain n → Ambient q} (hf : MemLp f 2 ν) :
      MemLp (f ∘ F) 2 μ := memLp_comp_of_map_le_smul hFm hc hmap hf
  have hcolumns {D : Domain n → Gradient n q}
      (hD : ∀ j, MemLp (fun y => D y j) 2 ν) (i : Fin m) :
      MemLp (fun x => ∑ j : Fin n, a i j x • D (F x) j) 2 μ := by
    have hL := memLp_finsetSum Finset.univ
      (fun j _ => (hcomp (hD j)).smul (r := (2 : ℝ≥0∞)) (ha i j))
    simpa only [Finset.sum_apply, Pi.smul_apply', Function.comp_def] using hL
  obtain ⟨f, hf, hfW, hfconv, hDfconv⟩ := hu.smoothDensity_memW12_ball hR
  let Df : ℕ → Domain m → Gradient m q := fun k x i =>
    ∑ j : Fin n, a i j x • coordinateDerivative (f k) (hf k) j (F x)
  have hW (k : ℕ) : MemW12 U (f k ∘ F) (Df k) := by
    exact ⟨hasWeakGradient_smooth_coordinate_pullback U hF (hf k), hcomp (hfW k).2.1,
      fun i => hcolumns (D := fun y j => coordinateDerivative (f k) (hf k) j y)
        (hfW k).2.2 i⟩
  apply MemW12.of_L2_limit (Df := Df)
    (Du := fun x i => ∑ j : Fin n, a i j x • Du (F x) j)
    hW (hcomp hu.2.1) (hcolumns (D := Du) hu.2.2)
  · exact tendsto_eLpNorm_comp_zero_of_map_le_smul hFm hc hmap
      (p := 2) (f := fun k => f k - u)
      (fun k => ((hfW k).2.1.sub hu.2.1).aestronglyMeasurable) hfconv
  · intro i
    have hcol (j : Fin n) : Tendsto (fun k => eLpNorm
        (fun x => a i j x •
          (coordinateDerivative (f k) (hf k) j (F x) - Du (F x) j)) 2 μ)
        atTop (𝓝 0) := by
      have hconv := tendsto_eLpNorm_comp_zero_of_map_le_smul hFm hc hmap
        (p := 2) (f := fun k y => coordinateDerivative (f k) (hf k) j y - Du y j)
        (fun k => ((hfW k).2.2 j |>.sub (hu.2.2 j)).aestronglyMeasurable) (hDfconv j)
      exact tendsto_eLpNorm_two_bounded_smul_zero (ha i j)
        (f := fun k x => coordinateDerivative (f k) (hf k) j (F x) - Du (F x) j)
        (fun k => (hcomp ((hfW k).2.2 j |>.sub (hu.2.2 j))).aestronglyMeasurable) hconv
    have hsum := tendsto_eLpNorm_two_finite_sum_zero
      (fun j k => ((hcomp ((hfW k).2.2 j |>.sub (hu.2.2 j))).smul
        (r := (2 : ℝ≥0∞)) (ha i j)).aestronglyMeasurable)
      hcol
    have heq (k : ℕ) : (fun x => Df k x i -
        ∑ j : Fin n, a i j x • Du (F x) j) =
        (fun x => ∑ j : Fin n, a i j x •
          (coordinateDerivative (f k) (hf k) j (F x) - Du (F x) j)) := by
      funext x
      simp only [Df, smul_sub, Finset.sum_sub_distrib]
    simpa only [heq, Pi.smul_apply', Function.comp_def, Pi.sub_apply] using hsum

end StratificationTheory
