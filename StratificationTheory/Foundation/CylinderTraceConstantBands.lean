module

public import StratificationTheory.Frozen.CylinderTraceCharacterization
public import StratificationTheory.Foundation.IntervalClosedConstraints

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- A literal constant left time band determines the named trace at its
right boundary, including an interior boundary of the original cylinder. -/
theorem cylinderTrace_eq_of_left_constant_band {n q : ℕ} (hn : 2 ≤ n)
    {a b t : ℝ} (hab : a < b) (hat : a < t) (htb : t ≤ b)
    (v : unitCylinder n a b → Ambient q) (hv : MemCylinderW12 hn hab v)
    (u : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ c : unitCylinder n a b, (e c.val).2 0 < t → v c = u ⟨(e c.val).1, c.property.1⟩) →
    cylinderTrace hn hab v hv ⟨t, hat.le, htb⟩ = hu.toLp u := by
  intro e hBand
  let H := cylinderTrace hn hab v hv
  let incl : C(Icc a t, Icc a b) :=
    ⟨fun s => ⟨s.val, s.property.1, s.property.2.trans htb⟩,
      continuous_subtype_val.subtype_mk _⟩
  let G : C(Icc a t, Lp (Ambient q) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))) := H.comp incl
  have hG : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo a t,
      G ⟨s, hs.1.le, hs.2.le⟩ ∈ ({hu.toLp u} : Set _) := by
    filter_upwards [(cylinderTrace_characterization hn hab v hv).1] with s hRaw
    intro hs
    obtain ⟨hSlice, hClass⟩ := hRaw ⟨hs.1, lt_of_lt_of_le hs.2 htb⟩
    change cylinderTrace hn hab v hv ⟨s, hs.1.le, hs.2.le.trans htb⟩ = hu.toLp u
    rw [hClass]
    apply MemLp.toLp_congr hSlice hu
    exact Eventually.of_forall fun θ => by
      have h := hBand ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) s),
        unitCylinder_param_mem θ ⟨s, hs.1.le, hs.2.le.trans htb⟩⟩ (by
          simpa only [e.apply_symm_apply, PiLp.single_apply, ite_true] using hs.2)
      simpa only [e.apply_symm_apply] using h
  exact continuous_interval_mem_closed_of_ae hat G isClosed_singleton hG ⟨t, hat.le, le_rfl⟩

/-- A literal constant right time band determines the named trace at its
left boundary, including an interior boundary of the original cylinder. -/
theorem cylinderTrace_eq_of_right_constant_band {n q : ℕ} (hn : 2 ≤ n)
    {a b t : ℝ} (hab : a < b) (hat : a ≤ t) (htb : t < b)
    (v : unitCylinder n a b → Ambient q) (hv : MemCylinderW12 hn hab v)
    (u : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ c : unitCylinder n a b, t < (e c.val).2 0 → v c = u ⟨(e c.val).1, c.property.1⟩) →
    cylinderTrace hn hab v hv ⟨t, hat, htb.le⟩ = hu.toLp u := by
  intro e hBand
  let H := cylinderTrace hn hab v hv
  let incl : C(Icc t b, Icc a b) :=
    ⟨fun s => ⟨s.val, hat.trans s.property.1, s.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let G : C(Icc t b, Lp (Ambient q) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))) := H.comp incl
  have hG : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo t b,
      G ⟨s, hs.1.le, hs.2.le⟩ ∈ ({hu.toLp u} : Set _) := by
    filter_upwards [(cylinderTrace_characterization hn hab v hv).1] with s hRaw
    intro hs
    obtain ⟨hSlice, hClass⟩ := hRaw ⟨lt_of_le_of_lt hat hs.1, hs.2⟩
    change cylinderTrace hn hab v hv ⟨s, hat.trans hs.1.le, hs.2.le⟩ = hu.toLp u
    rw [hClass]
    apply MemLp.toLp_congr hSlice hu
    exact Eventually.of_forall fun θ => by
      have h := hBand ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) s),
        unitCylinder_param_mem θ ⟨s, hat.trans hs.1.le, hs.2.le⟩⟩ (by
          simpa only [e.apply_symm_apply, PiLp.single_apply, ite_true] using hs.1)
      simpa only [e.apply_symm_apply] using h
  exact continuous_interval_mem_closed_of_ae htb G isClosed_singleton hG ⟨t, le_rfl, htb.le⟩

end StratificationTheory
