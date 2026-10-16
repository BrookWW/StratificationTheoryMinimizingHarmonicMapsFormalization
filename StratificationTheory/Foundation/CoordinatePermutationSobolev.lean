module

public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.SobolevL2Closure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate permutations of actual Sobolev data

Volume-preserving coordinate permutations transfer smooth graph approximations
and retain the corresponding permuted weak-gradient columns.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

/-- A coordinate permutation pulls back a finite Sobolev ball with the actual
permuted columns of its original weak-gradient witness. -/
theorem memW12_ball_coordinatePerm {n q : ℕ}
    {z : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain z R) u Du) (p : Equiv.Perm (Fin n)) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    MemW12 (ballDomain (Q.symm z) R) (fun x => u (Q x))
      (fun x i => Du (Q x) (p i)) := by
  intro Q
  have hm := Q.measurePreserving.restrict_preimage (measurableSet_ball (x := z) (ε := R))
  rw [Q.preimage_ball] at hm
  obtain ⟨m, hmSmooth, hmW, hmConv, hmDConv⟩ := hu.smoothDensity_memW12_ball hR
  let f : ℕ → Domain n → Ambient q := fun k x => m k (Q x)
  let Df : ℕ → Domain n → Gradient n q := fun k x i =>
    coordinateDerivative (m k) (hmSmooth k) (p i) (Q x)
  have hSmooth (k : ℕ) : ContDiff ℝ ∞ (f k) :=
    (hmSmooth k).comp Q.toContinuousLinearEquiv.contDiff
  have hD (k : ℕ) (i : Fin n) (x : Domain n) :
      coordinateDerivative (f k) (hSmooth k) i x = Df k x i := by
    have h := ((hmSmooth k).differentiable (by simp) (Q x)).hasFDerivAt.comp x
      Q.toContinuousLinearEquiv.hasFDerivAt
    change HasFDerivAt (f k) _ x at h
    change fderiv ℝ (f k) x (EuclideanSpace.single i 1) = _
    rw [h.fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ (m k) (Q x) (Q (EuclideanSpace.single i 1)) = _
    rw [LinearIsometryEquiv.piLpCongrLeft_single]
    rfl
  have hDfun (k : ℕ) (i : Fin n) : coordinateDerivative (f k) (hSmooth k) i =
      (fun x => Df k x i) := funext (hD k i)
  have hfLp (k : ℕ) : MemLp (f k) 2 (volume.restrict (ball (Q.symm z) R)) :=
    (hmW k).2.1.comp_measurePreserving hm
  have hDfLp (k : ℕ) (i : Fin n) : MemLp (fun x => Df k x i) 2
      (volume.restrict (ball (Q.symm z) R)) :=
    ((hmW k).2.2 (p i)).comp_measurePreserving hm
  have hfW (k : ℕ) : MemW12 (ballDomain (Q.symm z) R) (f k) (Df k) := by
    have hW := memW12_of_contDiff (ballDomain (Q.symm z) R) (hSmooth k) (hfLp k)
      (fun i => by rw [hDfun]; exact hDfLp k i)
    have hDall : (fun x i => coordinateDerivative (f k) (hSmooth k) i x) = Df k := by
      funext x i
      exact hD k i x
    rwa [hDall] at hW
  apply MemW12.of_L2_limit_ball (Q.symm z) R hfW
    (hu.2.1.comp_measurePreserving hm)
    (fun i => (hu.2.2 (p i)).comp_measurePreserving hm)
  · have heq (k : ℕ) : eLpNorm (f k - (fun x => u (Q x))) 2
        (volume.restrict (ball (Q.symm z) R)) =
        eLpNorm (m k - u) 2 (volume.restrict (ball z R)) := by
      have hcomp := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
        ((hmW k).2.1.sub hu.2.1).aestronglyMeasurable hm
      change eLpNorm ((m k - u) ∘ Q) 2
        (volume.restrict (ball (Q.symm z) R)) = _ at hcomp
      exact hcomp
    exact hmConv.congr (fun k => (heq k).symm)
  · intro i
    have heq (k : ℕ) : eLpNorm (fun x => Df k x i - Du (Q x) (p i)) 2
        (volume.restrict (ball (Q.symm z) R)) =
        eLpNorm (fun x => coordinateDerivative (m k) (hmSmooth k) (p i) x - Du x (p i))
          2 (volume.restrict (ball z R)) := by
      have hcomp := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
        (((hmW k).2.2 (p i)).sub (hu.2.2 (p i))).aestronglyMeasurable hm
      exact hcomp
    exact (hmDConv (p i)).congr (fun k => (heq k).symm)

end StratificationTheory
