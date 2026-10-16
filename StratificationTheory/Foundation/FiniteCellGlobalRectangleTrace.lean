module

public import StratificationTheory.Foundation.CoordinateRectangleTrace
public import StratificationTheory.Foundation.LpTwoMeasureRestriction
public import StratificationTheory.Foundation.RadialTraceCompatibility

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- Original native traces on an a.e. finite cover of the spatial base
identify both original global endpoint classes of the actual full weak
rectangle map. The global endpoint L2 qualifications are produced internally. -/
theorem exists_global_rectangle_trace_of_original_cell_traces {n q : ℕ}
    {I : Type*} [Fintype I] (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    (C : I → OpenDomain n) (hSub : ∀ j, (C j).val ⊆ U.val)
    (hCover : ∀ᵐ x ∂volume.restrict U.val, ∃ j : I, x ∈ (C j).val)
    {a b : ℝ} (hab : a < b)
    (W : Domain (n + 1) → Ambient q) (D : Domain (n + 1) → Gradient (n + 1) q)
    (g₀ g₁ : Domain n → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    MemW12 Ω W D →
    ∀ K : ∀ j : I, C(Icc a b, Lp (Ambient q) 2 (volume.restrict (C j).val)),
    (∀ j, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x : Domain n => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict (C j).val),
        K j ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ j, (K j ⟨a, le_rfl, hab.le⟩ : Domain n → Ambient q) =ᵐ[volume.restrict (C j).val] g₀) →
    (∀ j, (K j ⟨b, hab.le, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict (C j).val] g₁) →
    ∃ H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hs : MemLp (fun x : Domain n => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      (∃ hg₀ : MemLp g₀ 2 (volume.restrict U.val), H ⟨a, le_rfl, hab.le⟩ = hg₀.toLp g₀) ∧
      (∃ hg₁ : MemLp g₁ 2 (volume.restrict U.val), H ⟨b, hab.le, le_rfl⟩ = hg₁.toLp g₁) ∧
      ∀ J : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hs : MemLp (fun x : Domain n => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → J = H := by
  intro e Ω hW K hK hK₀ hK₁
  obtain ⟨H, hH, hUnique⟩ := exists_unique_L2_trace_of_memW12_rectangle U hab hW
  have hCell (j : I) :
      ((H ⟨a, le_rfl, hab.le⟩ : Domain n → Ambient q) =ᵐ[volume.restrict (C j).val] g₀) ∧
      ((H ⟨b, hab.le, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict (C j).val] g₁) := by
    let μ := (volume : Measure (Domain n)).restrict (C j).val
    let ν := (volume : Measure (Domain n)).restrict U.val
    have hμν : μ ≤ ν := Measure.restrict_mono_set volume (hSub j)
    let L : Lp (Ambient q) 2 ν →L[ℝ] Lp (Ambient q) 2 μ := Lp.LpToLpOfMeasureLeSMul
      (c := (1 : ℝ≥0∞)) (by norm_num) (by simpa only [one_smul] using hμν)
    let J : C(Icc a b, Lp (Ambient q) 2 μ) := ⟨fun t => L (H t), L.continuous.comp H.continuous⟩
    have hJ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hs : MemLp (fun x : Domain n => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 μ,
          J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
      filter_upwards [hH] with t ht htI
      obtain ⟨hs, hClass⟩ := ht htI
      have hsmall := hs.mono_measure hμν
      refine ⟨hsmall, ?_⟩
      change L (H ⟨t, htI.1.le, htI.2.le⟩) = _
      rw [hClass]
      exact lp_two_measure_restriction_toLp hμν _ hs hsmall
    have hEq : J = K j := continuous_Lp_representatives_eq_of_ae_slices
      (f := fun p : Domain n × ℝ => W (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      (g := fun p : Domain n × ℝ => W (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      hab J (K j) hJ (hK j) (Eventually.of_forall fun _ _ => EventuallyEq.rfl)
    have hCoe (r : Icc a b) : (K j r : Domain n → Ambient q) =ᵐ[μ] H r := by
      have h := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
        (by norm_num) (show μ ≤ (1 : ℝ≥0∞) • ν by simpa only [one_smul] using hμν) (H r)
      have hPoint : L (H r) = K j r := congrArg (fun M : C(Icc a b, Lp (Ambient q) 2 μ) => M r) hEq
      change (L (H r)) =ᵐ[μ] H r at h
      rwa [hPoint] at h
    exact ⟨(hCoe _).symm.trans (hK₀ j), (hCoe _).symm.trans (hK₁ j)⟩
  have hGlobal (r : Icc a b) (g : Domain n → Ambient q)
      (hEq : ∀ j, (H r : Domain n → Ambient q) =ᵐ[volume.restrict (C j).val] g) :
      (H r : Domain n → Ambient q) =ᵐ[volume.restrict U.val] g := by
    have hImp (j : I) : ∀ᵐ x : Domain n ∂volume, x ∈ (C j).val → H r x = g x :=
      (ae_restrict_iff' (C j).property.measurableSet).mp (hEq j)
    filter_upwards [hCover, ae_restrict_of_ae (ae_all_iff.mpr hImp)] with x hx hPx
    obtain ⟨j, hj⟩ := hx
    exact hPx j hj
  have hAE₀ := hGlobal ⟨a, le_rfl, hab.le⟩ g₀ (fun j => (hCell j).1)
  have hAE₁ := hGlobal ⟨b, hab.le, le_rfl⟩ g₁ (fun j => (hCell j).2)
  have hg₀ := (Lp.memLp (H ⟨a, le_rfl, hab.le⟩)).ae_eq hAE₀
  have hg₁ := (Lp.memLp (H ⟨b, hab.le, le_rfl⟩)).ae_eq hAE₁
  refine ⟨H, hH, ⟨hg₀, ?_⟩, ⟨hg₁, ?_⟩, hUnique⟩
  · apply Lp.ext
    exact hAE₀.trans hg₀.coeFn_toLp.symm
  · apply Lp.ext
    exact hAE₁.trans hg₁.coeFn_toLp.symm

end StratificationTheory
