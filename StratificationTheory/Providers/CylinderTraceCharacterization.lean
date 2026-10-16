module

public import StratificationTheory.Frozen.CylinderTrace
import StratificationTheory.Foundation.CylinderAECoordinates
import StratificationTheory.Foundation.CylinderAEClasses

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory.Providers.CylinderTraceCharacterization

/-- The named trace has the full original-slice characterization and uniqueness;
native-a.e. changes produce Sobolev membership and the same whole trace curve. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun p =>
      ⟨e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val), unitCylinder_param_mem p.1 p.2⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
        cylinderTrace hn hab v hv ⟨t, ht.1.le, ht.2.le⟩ =
          hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩)))) ∧
    (∀ H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩)))) →
      H = cylinderTrace hn hab v hv) ∧
    ∀ w : unitCylinder n a b → Ambient q,
      v =ᵐ[(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))] w →
      ∃ hw : MemCylinderW12 hn hab w,
        cylinderTrace hn hab w hw = cylinderTrace hn hab v hv :=
by
  intro e c σ
  have hspec := Classical.choose_spec (cylinder_trace_existsUnique hn hab v hv).exists
  refine ⟨hspec, ?_, ?_⟩
  · intro H hH
    exact ExistsUnique.unique (cylinder_trace_existsUnique hn hab v hv) hH hspec
  · intro w hvw
    have hw := memCylinderW12_congr_ae hn hab hv hvw
    refine ⟨hw, ?_⟩
    have hwspec := Classical.choose_spec (cylinder_trace_existsUnique hn hab w hw).exists
    exact (continuous_unitCylinder_representatives_eq_of_ae (by omega : 0 < n)
      hab v w hvw (cylinderTrace hn hab v hv) (cylinderTrace hn hab w hw)
      hspec hwspec).symm

end StratificationTheory.Providers.CylinderTraceCharacterization
