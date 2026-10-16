module

public import StratificationTheory.Foundation.IntervalSobolevProductBase
public import StratificationTheory.Interpolation.CylinderAffineGradient

/-!
# The actual weak graph of affine interpolation over an edge

Two closed-line representatives with their original L2 classes and integral
increments give a finite two-dimensional Sobolev map. Its spatial and time
columns retain the original derivative data and the same two representatives.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Original real-line data determine the full native rectangular Sobolev
graph of the literal affine-time interpolation. -/
theorem interval_pair_memW12_rectangle {q : ℕ}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F G f h g k : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h)
    (hFinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      G t - G s = ∫ y in s..t, k y) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let α : Domain 2 → ℝ := fun y => ((e y).2 0 - c) / (d - c)
    MemW12
      ⟨{y : Domain 2 | (e y).1 0 ∈ Ioo a b ∧ (e y).2 0 ∈ Ioo c d},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_fst.comp e.continuous))).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
      (fun y => (1 - α y) • F ((e y).1 0) + α y • G ((e y).1 0))
      (fun y => Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - α y) • g ((e y).1 0) + α y • k ((e y).1 0))
        (fun _ : Fin 1 => (d - c)⁻¹ • (G ((e y).1 0) - F ((e y).1 0)))) := by
  intro e α
  let O : OpenDomain 1 := ⟨{x : Domain 1 | x 0 ∈ Ioo a b},
    isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous⟩
  have hFW : MemW12 O (fun x => F (x 0)) (fun x _ => g (x 0)) :=
    memW12_domainOne_of_integral_increments hab hf hg hFae hFinc
  have hGW : MemW12 O (fun x => G (x 0)) (fun x _ => k (x 0)) :=
    memW12_domainOne_of_integral_increments hab hh hk hGae hGinc
  have hprod := MemW12.cylinder_affine_gradient (n := 1) (q := q) O
    (volume_domainOne_interval_ne_top a b) hcd hFW hGW
  exact hprod

end StratificationTheory
