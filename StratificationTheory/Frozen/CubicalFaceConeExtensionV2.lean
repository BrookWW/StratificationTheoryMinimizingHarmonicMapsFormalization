-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.Basic

import StratificationTheory.Providers.CubicalFaceConeExtensionV2

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

theorem cubical_face_cone_extension_joint {n q : ℕ} (hn : 2 ≤ n)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w Dw) :
    let B : OpenDomain n :=
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let C : OpenDomain (n + 1) :=
      ⟨T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ i : Fin n, {y : Domain (n + 1) | |X y i| < T y},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_lt (((EuclideanSpace.proj i).continuous.comp
            (continuous_fst.comp e.continuous)).abs)
            ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous))))⟩
    let W : Domain (n + 1) → Ambient q := fun y => w (ξ y)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun i : Fin n => (T y)⁻¹ • Dw (ξ y) i)
        (fun _last : Fin 1 => -((T y)⁻¹ • (∑ i : Fin n, (ξ y) i • Dw (ξ y) i)))
    MemW12 C W D ∧
    (∀ y ∈ C.val, ξ y ∈ B.val) ∧
    (∀ (ψ : Domain (n + 1) → ℝ≥0∞), AEMeasurable ψ (volume.restrict C.val) →
      (∫⁻ y in C.val, ψ y) =
        ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ n) *
          ∫⁻ x in B.val, ψ (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r))) ∧
    Integrable (fun y => ‖W y‖ ^ 2) (volume.restrict C.val) ∧
    (∫ y in C.val, ‖W y‖ ^ 2) =
      ((n : ℝ) + 1)⁻¹ * ∫ x in B.val, ‖w x‖ ^ 2 ∧
    Integrable (fun y => hsNormSq (D y)) (volume.restrict C.val) ∧
    (∫ y in C.val, hsNormSq (D y)) =
      ((n : ℝ) - 1)⁻¹ * ∫ x in B.val,
        hsNormSq (Dw x) + ‖∑ i : Fin n, x i • Dw x i‖ ^ 2 ∧
    (∫ y in C.val, hsNormSq (D y)) ≤
      (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Dw x) ∧
    (∀ x ∈ B.val, ∀ r ∈ Ioc (0 : ℝ) 1,
      W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)) = w x) ∧
    ∀ (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) 1),
      ∃ H : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ r : Icc ρ 1, H r = hw.2.1.toLp w) ∧
        (∀ r : Icc ρ 1,
          ∃ hr : MemLp (fun x => W (e.symm (r.val • x,
              EuclideanSpace.single (0 : Fin 1) r.val))) 2 (volume.restrict B.val),
            H r = hr.toLp (fun x => W (e.symm (r.val • x,
              EuclideanSpace.single (0 : Fin 1) r.val)))) ∧
        H ⟨1, hρ.2.le, le_rfl⟩ = hw.2.1.toLp w ∧
        ∀ K : C(Icc ρ 1, Lp (Ambient q) 2 (volume.restrict B.val)),
          (∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo ρ 1,
            ∃ hslice : MemLp (fun x => W (e.symm (r • x,
                EuclideanSpace.single (0 : Fin 1) r))) 2 (volume.restrict B.val),
              K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp
                (fun x => W (e.symm (r • x, EuclideanSpace.single (0 : Fin 1) r)))) → K = H :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.CubicalFaceConeExtensionV2.result hn hw
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
