module

public import StratificationTheory.Frozen.CylinderTraceCharacterization
public import StratificationTheory.Foundation.CylinderSobolevAlgebra
import StratificationTheory.Foundation.CylinderAECoordinates

/-!
# Algebra and closed constraints for the named cylinder trace

The complete original-slice characterization identifies traces of linear
operations on full cylinder Sobolev maps. A closed native-a.e. value constraint
on the original map is retained at every closed-interval time.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- The named trace commutes with every real scalar, including zero. -/
theorem cylinderTrace_const_smul {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) (r : ℝ) :
    cylinderTrace hn hab (fun y => r • v y) (memCylinderW12_const_smul hn hab r hv) =
      r • cylinderTrace hn hab v hv := by
  apply Eq.symm
  apply (cylinderTrace_characterization hn hab (fun y => r • v y)
    (memCylinderW12_const_smul hn hab r hv)).2.1
  filter_upwards [(cylinderTrace_characterization hn hab v hv).1] with t ht htI
  obtain ⟨hL, hEq⟩ := ht htI
  refine ⟨hL.const_smul r, ?_⟩
  change r • cylinderTrace hn hab v hv ⟨t, htI.1.le, htI.2.le⟩ = _
  rw [hEq]
  exact (MemLp.toLp_const_smul r hL).symm

/-- Traces of differences use the same two named curves on the full interval. -/
theorem cylinderTrace_sub {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : unitCylinder n a b → Ambient q)
    (hu : MemCylinderW12 hn hab u) (hv : MemCylinderW12 hn hab v) :
    cylinderTrace hn hab (u - v) (memCylinderW12_sub hn hab hu hv) =
      cylinderTrace hn hab u hu - cylinderTrace hn hab v hv := by
  apply Eq.symm
  apply (cylinderTrace_characterization hn hab (u - v)
    (memCylinderW12_sub hn hab hu hv)).2.1
  filter_upwards [(cylinderTrace_characterization hn hab u hu).1,
    (cylinderTrace_characterization hn hab v hv).1] with t hUt hVt ht
  obtain ⟨hU, hUeq⟩ := hUt ht
  obtain ⟨hV, hVeq⟩ := hVt ht
  refine ⟨hU.sub hV, ?_⟩
  change cylinderTrace hn hab u hu ⟨t, ht.1.le, ht.2.le⟩ -
    cylinderTrace hn hab v hv ⟨t, ht.1.le, ht.2.le⟩ = _
  rw [hUeq, hVeq]
  exact (hU.toLp_sub hV).symm

/-- Traces of sums use the same two named curves on the full interval. -/
theorem cylinderTrace_add {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : unitCylinder n a b → Ambient q)
    (hu : MemCylinderW12 hn hab u) (hv : MemCylinderW12 hn hab v) :
    cylinderTrace hn hab (u + v) (memCylinderW12_add hn hab hu hv) =
      cylinderTrace hn hab u hu + cylinderTrace hn hab v hv := by
  apply Eq.symm
  apply (cylinderTrace_characterization hn hab (u + v)
    (memCylinderW12_add hn hab hu hv)).2.1
  filter_upwards [(cylinderTrace_characterization hn hab u hu).1,
    (cylinderTrace_characterization hn hab v hv).1] with t hUt hVt ht
  obtain ⟨hU, hUeq⟩ := hUt ht
  obtain ⟨hV, hVeq⟩ := hVt ht
  refine ⟨hU.add hV, ?_⟩
  change cylinderTrace hn hab u hu ⟨t, ht.1.le, ht.2.le⟩ +
    cylinderTrace hn hab v hv ⟨t, ht.1.le, ht.2.le⟩ = _
  rw [hUeq, hVeq]
  exact (hU.toLp_add hV).symm

/-- A closed value constraint on the original native cylinder class holds
for the named trace at all times, including both endpoints. -/
theorem cylinderTrace_mem_closed {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) {S : Set (Ambient q)} (hS : IsClosed S)
    (hvalues : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n :
      Measure (unitCylinder n a b)), v y ∈ S) :
    ∀ t : Icc a b, ∀ᵐ θ : sphere (0 : Domain n) 1
      ∂Measure.euclideanHausdorffMeasure (n - 1),
        cylinderTrace hn hab v hv t θ ∈ S := by
  exact continuous_unitCylinder_representative_mem_closed (by omega : 0 < n)
    hab v hS hvalues (cylinderTrace hn hab v hv)
    (cylinderTrace_characterization hn hab v hv).1

end StratificationTheory
