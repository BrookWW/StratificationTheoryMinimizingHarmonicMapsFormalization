module

public import StratificationTheory.Frozen.CylinderTraceCharacterization
public import StratificationTheory.Foundation.CylinderSurfaceMeasure
public import HarmonicMaps.SobolevRestriction

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Restricting the original native cylinder to a genuine closed time
subinterval preserves native Sobolev membership. -/
theorem memCylinderW12_time_restriction {n q : ℕ} (hn : 2 ≤ n)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) (has : a ≤ s) (htb : t ≤ b)
    (v : unitCylinder n a b → Ambient q) (hv : MemCylinderW12 hn hab v) :
    let incl : unitCylinder n s t → unitCylinder n a b := fun c =>
      ⟨c.val, c.property.1, has.trans c.property.2.1, c.property.2.2.trans htb⟩
    let w : unitCylinder n s t → Ambient q := v ∘ incl
    MemCylinderW12 hn hst w := by
  intro incl w
  let μ : Measure (unitCylinder n s t) := Measure.euclideanHausdorffMeasure n
  let ν : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
  have hIso : Isometry incl := fun c d => rfl
  have hMap : Measure.map incl μ ≤ ν := by
    rw [hIso.map_euclideanHausdorffMeasure]
    exact Measure.restrict_le_self
  have hLp : MemLp w 2 μ :=
    (hv.1.mono_measure hMap).comp_of_map hIso.continuous.measurable.aemeasurable
  have hvCopy := hv
  obtain ⟨_hVLp, U, hSphere, hZero, V, D, hV, hVRaw⟩ := hvCopy
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo s t},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hSub : Ω.val ⊆ {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b} := by
    intro y hy
    exact ⟨hy.1, lt_of_le_of_lt has hy.2.1, lt_of_lt_of_le hy.2.2 htb⟩
  have hVSub : MemW12 Ω V D :=
    ⟨hV.1.mono hSub, hV.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => (hV.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  have hw : MemCylinderW12 hn hst w :=
    ⟨hLp, U, hSphere, hZero, V, D, hVSub, by
      intro ρ c hc hρ
      exact hVRaw ρ (incl c) ⟨lt_of_le_of_lt has hc.1, lt_of_lt_of_le hc.2 htb⟩ hρ⟩
  exact hw

private theorem raw_curve_closed_time_restriction {X : Type*} [MeasurableSpace X]
    {q : ℕ} (μ : Measure X) {a b s t : ℝ} (has : a ≤ s) (htb : t ≤ b)
    (f : Icc a b → X → Ambient q) (Γ : C(Icc a b, Lp (Ambient q) 2 μ))
    (hRaw : ∀ᵐ τ : ℝ ∂volume, ∀ hτ : τ ∈ Ioo a b,
      ∃ hs : MemLp (f ⟨τ, hτ.1.le, hτ.2.le⟩) 2 μ,
        Γ ⟨τ, hτ.1.le, hτ.2.le⟩ = hs.toLp (f ⟨τ, hτ.1.le, hτ.2.le⟩)) :
    let timeIncl : C(Icc s t, Icc a b) :=
      ⟨fun τ => ⟨τ.val, has.trans τ.property.1, τ.property.2.trans htb⟩,
        continuous_subtype_val.subtype_mk (fun τ =>
          ⟨has.trans τ.property.1, τ.property.2.trans htb⟩)⟩
    ∀ᵐ τ : ℝ ∂volume, ∀ hτ : τ ∈ Ioo s t,
      ∃ hs : MemLp (f (timeIncl ⟨τ, hτ.1.le, hτ.2.le⟩)) 2 μ,
        (Γ.comp timeIncl) ⟨τ, hτ.1.le, hτ.2.le⟩ =
          hs.toLp (f (timeIncl ⟨τ, hτ.1.le, hτ.2.le⟩)) := by
  intro timeIncl
  filter_upwards [hRaw] with τ hτ ht
  exact hτ ⟨lt_of_le_of_lt has ht.1, lt_of_lt_of_le ht.2 htb⟩

private theorem named_cylinder_trace_eq_of_closed_raw {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let f : Icc a b → sphere (0 : Domain n) 1 → Ambient q := fun τ θ =>
      v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩
    ∀ H : C(Icc a b, Lp (Ambient q) 2 σ),
    (∀ᵐ τ : ℝ ∂volume, ∀ hτ : τ ∈ Ioo a b,
      ∃ hs : MemLp (f ⟨τ, hτ.1.le, hτ.2.le⟩) 2 σ,
        H ⟨τ, hτ.1.le, hτ.2.le⟩ = hs.toLp (f ⟨τ, hτ.1.le, hτ.2.le⟩)) →
    H = cylinderTrace hn hab v hv := by
  intro e σ f H hRaw
  with_reducible exact (cylinderTrace_characterization hn hab v hv).2.1 H hRaw

/-- Restricting the original native cylinder to a genuine closed time
subinterval preserves Sobolev membership and the entire named trace curve. -/
theorem exists_cylinder_time_restriction {n q : ℕ} (hn : 2 ≤ n)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) (has : a ≤ s) (htb : t ≤ b)
    (v : unitCylinder n a b → Ambient q) (hv : MemCylinderW12 hn hab v) :
    let incl : unitCylinder n s t → unitCylinder n a b := fun c =>
      ⟨c.val, c.property.1, has.trans c.property.2.1, c.property.2.2.trans htb⟩
    let w : unitCylinder n s t → Ambient q := v ∘ incl
    ∃ hw : MemCylinderW12 hn hst w, ∀ τ : Icc s t,
      cylinderTrace hn hst w hw τ =
        cylinderTrace hn hab v hv ⟨τ.val, has.trans τ.property.1, τ.property.2.trans htb⟩ := by
  intro incl w
  have hw : MemCylinderW12 hn hst w :=
    memCylinderW12_time_restriction hn hab hst has htb v hv
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let f : Icc a b → sphere (0 : Domain n) 1 → Ambient q := fun τ θ =>
    v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩
  let g : Icc s t → sphere (0 : Domain n) 1 → Ambient q := fun τ θ =>
    w ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩
  have hOriginalRaw : ∀ᵐ τ : ℝ ∂volume, ∀ hτ : τ ∈ Ioo a b,
      ∃ hs : MemLp (f ⟨τ, hτ.1.le, hτ.2.le⟩) 2 σ,
        cylinderTrace hn hab v hv ⟨τ, hτ.1.le, hτ.2.le⟩ =
          hs.toLp (f ⟨τ, hτ.1.le, hτ.2.le⟩) := by
    with_reducible exact (cylinderTrace_characterization hn hab v hv).1
  generalize hLarge : cylinderTrace hn hab v hv = Γ at hOriginalRaw ⊢
  have hTimeIncl (τ : Icc s t) : τ.val ∈ Icc a b :=
    ⟨has.trans τ.property.1, τ.property.2.trans htb⟩
  let timeIncl : C(Icc s t, Icc a b) :=
    ⟨fun τ => ⟨τ.val, hTimeIncl τ⟩, continuous_subtype_val.subtype_mk hTimeIncl⟩
  let H : C(Icc s t, Lp (Ambient q) 2 σ) := Γ.comp timeIncl
  have hRaw := raw_curve_closed_time_restriction σ has htb f Γ hOriginalRaw
  have hfg (τ : Icc s t) : g τ = f (timeIncl τ) := by
    funext θ
    rfl
  have hRawSmall : ∀ᵐ τ : ℝ ∂volume, ∀ hτ : τ ∈ Ioo s t,
      ∃ hs : MemLp (g ⟨τ, hτ.1.le, hτ.2.le⟩) 2 σ,
        H ⟨τ, hτ.1.le, hτ.2.le⟩ = hs.toLp (g ⟨τ, hτ.1.le, hτ.2.le⟩) := by
    simpa only [hfg, H] using hRaw
  have hH : H = cylinderTrace hn hst w hw :=
    named_cylinder_trace_eq_of_closed_raw hn hst w hw H hRawSmall
  refine ⟨hw, ?_⟩
  intro τ
  exact (congrArg (fun K => K τ) hH).symm

end StratificationTheory
