module

public import StratificationTheory.Foundation.CylinderPostcomposition
public import StratificationTheory.Frozen.CylinderTraceCharacterization

/-!
# Smooth postcomposition of the complete named cylinder trace

The same smooth map acts continuously on native L2 classes. Original interior
slice normalization therefore determines the postcomposed named trace on the
whole closed interval, including both endpoints.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff

namespace StratificationTheory

/-- Smooth postcomposition with globally bounded derivative commutes with the
complete named trace. The output L2 membership is produced at every time. -/
theorem cylinderTrace_postcompose {n q k : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) (F : Ambient q → Ambient k)
    (hF : ContDiff ℝ ∞ F) (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    ∀ t : Icc a b,
      ∃ hL : MemLp (F ∘ cylinderTrace hn hab v hv t) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        cylinderTrace hn hab (F ∘ v) (memCylinderW12_postcompose hn hab v hv F hF L hDF) t =
          hL.toLp (F ∘ cylinderTrace hn hab v hv t) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  let T : Lp (Ambient q) 2 σ → Lp (Ambient k) 2 σ := fun f =>
    (memLp_postcomposition (Lp.memLp f) hF hDF).toLp (F ∘ f)
  let H : C(Icc a b, Lp (Ambient k) 2 σ) :=
    ⟨fun t => T (cylinderTrace hn hab v hv t),
      (continuous_L2_smooth_postcomposition σ F hF L hDF).comp
        (cylinderTrace hn hab v hv).continuous⟩
  have hH : H = cylinderTrace hn hab (F ∘ v)
      (memCylinderW12_postcompose hn hab v hv F hF L hDF) := by
    apply (cylinderTrace_characterization hn hab (F ∘ v)
      (memCylinderW12_postcompose hn hab v hv F hF L hDF)).2.1
    filter_upwards [(cylinderTrace_characterization hn hab v hv).1] with t ht htI
    obtain ⟨hV, hVeq⟩ := ht htI
    refine ⟨memLp_postcomposition hV hF hDF, ?_⟩
    change T (cylinderTrace hn hab v hv ⟨t, htI.1.le, htI.2.le⟩) = _
    rw [hVeq]
    apply Lp.ext
    filter_upwards [(memLp_postcomposition (Lp.memLp (hV.toLp _)) hF hDF).coeFn_toLp,
      (memLp_postcomposition hV hF hDF).coeFn_toLp, hV.coeFn_toLp]
      with θ hleft hright hvalue
    exact hleft.trans ((congrArg F hvalue).trans hright.symm)
  intro t
  refine ⟨memLp_postcomposition (Lp.memLp (cylinderTrace hn hab v hv t)) hF hDF, ?_⟩
  rw [← hH]
  rfl

end StratificationTheory
