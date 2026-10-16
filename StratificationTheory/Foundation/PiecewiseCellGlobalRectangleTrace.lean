module

public import StratificationTheory.Foundation.FiniteCellGlobalRectangleTrace

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Original physical cell curves determine the global temporal endpoints
of their actual piecewise rectangle map. Their normalization by the same
global map is derived from the literal interior cell agreement. -/
theorem exists_global_rectangle_trace_of_piecewise_cell_traces {n q : ℕ}
    {I : Type*} [Fintype I] (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    (C : I → OpenDomain n) (hSub : ∀ j, (C j).val ⊆ U.val)
    (hCover : ∀ᵐ x ∂volume.restrict U.val, ∃ j : I, x ∈ (C j).val)
    {a b : ℝ} (hab : a < b)
    (u : I → Domain (n + 1) → Ambient q)
    (W : Domain (n + 1) → Ambient q) (D : Domain (n + 1) → Gradient (n + 1) q)
    (g₀ g₁ : Domain n → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    MemW12 Ω W D →
    (∀ j x, x ∈ (C j).val → ∀ t ∈ Ioo a b,
      W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
        u j (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) →
    ∀ K : ∀ j : I, C(Icc a b, Lp (Ambient q) 2 (volume.restrict (C j).val)),
    (∀ j, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x : Domain n => u j (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict (C j).val),
        K j ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u j (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
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
  intro e Ω hW hPoint K hK hK₀ hK₁
  apply exists_global_rectangle_trace_of_original_cell_traces U C hSub hCover hab W D g₀ g₁ hW K _ hK₀ hK₁
  intro j
  filter_upwards [hK j] with t ht htI
  obtain ⟨hs, hClass⟩ := ht htI
  have hRaw : (fun x : Domain n => u j (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
      =ᵐ[volume.restrict (C j).val] (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
    filter_upwards [ae_restrict_mem (C j).property.measurableSet] with x hx
    exact (hPoint j x hx t htI).symm
  have hs' := hs.ae_eq hRaw
  exact ⟨hs', hClass.trans (MemLp.toLp_congr hs hs' hRaw)⟩

end StratificationTheory
