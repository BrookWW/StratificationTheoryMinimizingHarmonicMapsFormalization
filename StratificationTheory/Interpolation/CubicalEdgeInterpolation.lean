module

public import StratificationTheory.Interpolation.CubicalEdgeInterpolationEnergy
public import StratificationTheory.Interpolation.CubicalEdgeInterpolationBounds
public import StratificationTheory.Interpolation.CubicalEdgeInterpolationTrace

/-!
# Joint rectangular interpolation from closed-line Sobolev data

One literal affine-time map has the full native weak graph, both quadratic
integral bounds, exact endpoint values and whole-closed-rectangle distance
bounds. The closed constraint is inherited from the original line a.e. data.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Two actual closed-line representatives and their original finite weak
data give one affine rectangular map with its displayed gradient, native
energy, discrepancy integral and pointwise closed-target distance bounds. -/
theorem interval_pair_rectangle_interpolation {q : ℕ}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F G f h g k : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo a b)))
    (hFAC : AbsolutelyContinuousOnInterval F a b)
    (hGAC : AbsolutelyContinuousOnInterval G a b)
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h)
    (hFinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      G t - G s = ∫ y in s..t, k y)
    {N : Set (Ambient q)} (hN : IsClosed N)
    (hfN : ∀ᵐ s ∂volume.restrict (Ioo a b), f s ∈ N)
    (hhN : ∀ᵐ s ∂volume.restrict (Ioo a b), h s ∈ N) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let α : Domain 2 → ℝ := fun y => ((e y).2 0 - c) / (d - c)
    let Ω : OpenDomain 2 :=
      ⟨{y : Domain 2 | (e y).1 0 ∈ Ioo a b ∧ (e y).2 0 ∈ Ioo c d},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_fst.comp e.continuous))).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
    let W : Domain 2 → Ambient q := fun y =>
      (1 - α y) • F ((e y).1 0) + α y • G ((e y).1 0)
    let DW : Domain 2 → Gradient 2 q := fun y =>
      Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - α y) • g ((e y).1 0) + α y • k ((e y).1 0))
        (fun _ : Fin 1 => (d - c)⁻¹ • (G ((e y).1 0) - F ((e y).1 0)))
    let D := ∫ s in Ioo a b, ‖f s - h s‖ ^ 2
    let A := ∫ s in Ioo a b, ‖g s‖ ^ 2 + ‖k s‖ ^ 2
    MemW12 Ω W DW ∧
    Integrable (fun y => hsNormSq (DW y)) (volume.restrict Ω.val) ∧
    (∫ y in Ω.val, hsNormSq (DW y)) ≤
      ((d - c) / 2) * ((∫ s in Ioo a b, ‖g s‖ ^ 2) + ∫ s in Ioo a b, ‖k s‖ ^ 2) +
      (d - c)⁻¹ * D ∧
    (∫ y in Ω.val, ‖DW y (Fin.natAdd 1 (0 : Fin 1))‖ ^ 2) = (d - c)⁻¹ * D ∧
    Integrable (fun y => ‖W y - F ((e y).1 0)‖ ^ 2) (volume.restrict Ω.val) ∧
    (∫ y in Ω.val, ‖W y - F ((e y).1 0)‖ ^ 2) ≤ ((d - c) / 2) * D ∧
    (∀ s : ℝ,
      W (e.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) c)) = F s ∧
      W (e.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) d)) = G s) ∧
    (∀ y : Domain 2, (e y).1 0 ∈ Icc a b → (e y).2 0 ∈ Icc c d →
      F ((e y).1 0) ∈ N ∧ G ((e y).1 0) ∈ N ∧
      ‖W y - F ((e y).1 0)‖ ^ 2 ≤ (4 / (b - a)) * D + 4 * Real.sqrt (2 * D * A) ∧
      (infDist (W y) N) ^ 2 ≤ D / (b - a) + Real.sqrt (2 * D * A)) ∧
    ∃ H : C(Icc c d, Lp (Ambient q) 2 (volume.restrict (Ioo a b))),
      (∀ t : Icc c d, H t = (1 - ((t : ℝ) - c) / (d - c)) • hf.toLp f +
        (((t : ℝ) - c) / (d - c)) • hh.toLp h) ∧
      (∀ t : Icc c d,
        ∃ ht : MemLp (fun s => W (e.symm (EuclideanSpace.single (0 : Fin 1) s,
            EuclideanSpace.single (0 : Fin 1) t.val))) 2 (volume.restrict (Ioo a b)),
          H t = ht.toLp (fun s => W (e.symm (EuclideanSpace.single (0 : Fin 1) s,
            EuclideanSpace.single (0 : Fin 1) t.val)))) ∧
      H ⟨c, le_rfl, hcd.le⟩ = hf.toLp f ∧
      H ⟨d, hcd.le, le_rfl⟩ = hh.toLp h ∧
      ∀ K : C(Icc c d, Lp (Ambient q) 2 (volume.restrict (Ioo a b))),
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c d,
          ∃ hslice : MemLp (fun s => W (e.symm (EuclideanSpace.single (0 : Fin 1) s,
              EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict (Ioo a b)),
            K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp
              (fun s => W (e.symm (EuclideanSpace.single (0 : Fin 1) s,
                EuclideanSpace.single (0 : Fin 1) t)))) → K = H := by
  intro e α Ω W DW D A
  have hgraph := interval_pair_memW12_rectangle hab hcd hf hh hg hk hFae hGae hFinc hGinc
  have henergy := interval_pair_rectangle_gradient_energy hcd hf hh hg hk hFae hGae
  have hδ := interval_pair_rectangle_discrepancy_energy hcd hf hh hFae hGae
  have hpoint := interval_affine_pair_pointwise_bounds hab hcd hf hh hg hk hFAC hGAC
    hFae hGae hFinc hGinc hN hfN hhN
  refine ⟨hgraph, henergy.1, henergy.2.1, henergy.2.2, hδ.1, hδ.2, ?_, ?_, ?_⟩
  · intro s
    simpa only [W, α, e.apply_symm_apply, PiLp.single_apply, ite_true] using hpoint.1 s
  · intro y hs ht
    exact hpoint.2 ((e y).1 0) hs ((e y).2 0) ht
  · have htrace := affine_pair_continuous_lp_trace (volume.restrict (Ioo a b)) hcd
      hf hh hFae hGae
    simpa only [W, α, e.apply_symm_apply, PiLp.single_apply, ite_true] using htrace

end StratificationTheory
