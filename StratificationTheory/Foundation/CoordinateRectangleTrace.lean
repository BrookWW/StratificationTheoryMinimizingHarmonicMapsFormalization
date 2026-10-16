module

public import StratificationTheory.Foundation.CoordinateL2Trace
public import StratificationTheory.Foundation.CylinderRawTime

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

/-- Original full Sobolev data on a finite rectangle produce the unique
continuous native L2 curve normalized by its original interior raw slices. -/
theorem exists_unique_L2_trace_of_memW12_rectangle {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {a b : ℝ} (hab : a < b)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12
      ⟨{y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp
              (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)))⟩ u Du) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ := (volume : Measure (Domain n)).restrict U.val
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp
          (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
  intro e σ
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := isFiniteMeasure_restrict.mp inferInstance
  have hm := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage Ω.property.measurableSet
  have hpre : (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ⁻¹' Ω.val = U.val ×ˢ Ioo a b := by
    ext p
    simp only [Ω, mem_preimage, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply,
      PiLp.single_apply, ↓reduceIte, mem_prod]
  rw [hpre, ← Measure.prod_restrict] at hm
  let f : Domain n × ℝ → Ambient q := fun p =>
    u (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  let g : Domain n × ℝ → Ambient q := fun p =>
    Du (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) (Fin.natAdd n (0 : Fin 1))
  have hf : MemLp f 2 (σ.prod (volume.restrict (Ioo a b))) := hu.2.1.comp_measurePreserving hm
  have hg : MemLp g 2 (σ.prod (volume.restrict (Ioo a b))) :=
    (hu.2.2 (Fin.natAdd n (0 : Fin 1))).comp_measurePreserving hm
  have htime : (volume : Measure ℝ).restrict (Icc a b) = volume.restrict (Ioo a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hfC : MemLp f 2 (σ.prod (volume.restrict (Icc a b))) := by rwa [htime]
  have hgC : MemLp g 2 (σ.prod (volume.restrict (Icc a b))) := by rwa [htime]
  apply exists_unique_finite_lp_continuous_representative_of_raw_time_identity σ hab hfC hgC
  intro φ hφ hcφ hsφ
  have hae := MemW12.cylinder_time_test_ae U hUfinite hu hφ hcφ hsφ
  filter_upwards [hae] with x hx
  have hφL : MemLp φ ∞ (volume.restrict (Ioo a b)) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφL : MemLp (deriv φ) ∞ (volume.restrict (Ioo a b)) :=
    (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hcφ.deriv _
  have hleft : Integrable (fun t => deriv φ t • f (x, t)) (volume.restrict (Ioo a b)) :=
    hx.1.smul_of_top_right hdφL
  have hright : Integrable (fun t => φ t • g (x, t)) (volume.restrict (Ioo a b)) :=
    hx.2.1.smul_of_top_right hφL
  have hid := hx.2.2.2
  change (∫ t in Ioo a b, deriv φ t • f (x, t) + φ t • g (x, t)) = 0 at hid
  rw [integral_add hleft hright] at hid
  rw [htime]
  exact eq_neg_iff_add_eq_zero.mpr hid

end StratificationTheory
