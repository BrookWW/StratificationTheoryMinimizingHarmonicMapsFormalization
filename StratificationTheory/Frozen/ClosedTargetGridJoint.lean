-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

import StratificationTheory.Providers.ClosedTargetGridJoint

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

theorem full_grid_closed_target_sobolev_pair_joint {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u v : Domain (n + 1) → Ambient q}
    {Du Dv : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv)
    {N : Set (Ambient q)} (hN : IsClosed N)
    (huN : ∀ᵐ y ∂volume.restrict (ball z R), u y ∈ N)
    (hvN : ∀ᵐ y ∂volume.restrict (ball z R), v y ∈ N)
    (S : Fin (n + 1) → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (Fin.natAdd n (0 : Fin 1)) i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R)
    {ε : ℝ} (hε : 0 < ε) :
    let p := fun i : Fin (n + 1) => Equiv.swap (Fin.natAdd n (0 : Fin 1)) i
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := fun i => {y : Domain (n + 1) |
      (e ((Q i).symm y)).1 ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let c := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let β := fun i y => (e ((Q i).symm y)).1
    let E := (ball z R).indicator (fun y => ENNReal.ofReal (hsNormSq (Du y) + hsNormSq (Dv y)))
    let Δ := (ball z R).indicator (fun y => ENNReal.ofReal (‖u y - v y‖ ^ 2))
    let basis := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _i : Fin (n + 1) => ε) (fun _i => hε.ne'.isUnit)
    ∃ Wu Wv : Fin (n + 1) → Domain (n + 1) → Ambient q,
      (∀ i, AEStronglyMeasurable (Wu i) (volume.restrict (Ω i)) ∧
        AEStronglyMeasurable (Wv i) (volume.restrict (Ω i)) ∧
        Wu i =ᵐ[volume.restrict (Ω i)] u ∧ Wv i =ᵐ[volume.restrict (Ω i)] v) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (S i),
        MemLp (fun t => u (c i x t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        MemLp (fun t => v (c i x t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        MemLp (fun t => Du (c i x t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        MemLp (fun t => Dv (c i x t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        AbsolutelyContinuousOnInterval (fun t => Wu i (c i x t)) (a i) (b i) ∧
        AbsolutelyContinuousOnInterval (fun t => Wv i (c i x t)) (a i) (b i) ∧
        (fun t => Wu i (c i x t)) =ᵐ[volume.restrict (Ioo (a i) (b i))] (fun t => u (c i x t)) ∧
        (fun t => Wv i (c i x t)) =ᵐ[volume.restrict (Ioo (a i) (b i))] (fun t => v (c i x t)) ∧
        (∀ t ∈ Icc (a i) (b i), Wu i (c i x t) ∈ N ∧ Wv i (c i x t) ∈ N) ∧
        ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
          (Wu i (c i x t) - Wu i (c i x s) = ∫ r in s..t, Du (c i x r) i) ∧
          (Wv i (c i x t) - Wv i (c i x s) = ∫ r in s..t, Dv (c i x r) i)) ∧
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i, y ∈ Ω i →
          Wu i y = u y ∧ Wv i y = v y ∧
          MemLp (fun t => u (c i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          MemLp (fun t => v (c i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          MemLp (fun t => Du (c i (β i y) t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          MemLp (fun t => Dv (c i (β i y) t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
          AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
          (fun t => Wu i (c i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
            (fun t => u (c i (β i y) t)) ∧
          (fun t => Wv i (c i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
            (fun t => v (c i (β i y) t)) ∧
          (∀ t ∈ Icc (a i) (b i), Wu i (c i (β i y) t) ∈ N ∧ Wv i (c i (β i y) t) ∈ N) ∧
          ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
            (Wu i (c i (β i y) t) - Wu i (c i (β i y) s) = ∫ r in s..t, Du (c i (β i y) r) i) ∧
            (Wv i (c i (β i y) t) - Wv i (c i (β i y) s) = ∫ r in s..t, Dv (c i (β i y) r) i)) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i j, y ∈ Ω i → y ∈ Ω j → Wu i y = Wu j y ∧ Wv i y = Wv j y) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), (∫⁻ t in Ico (0 : ℝ) ε, E (WithLp.toLp 2 (((l : Fin (n + 1) → ℝ) + offset) + t • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ))))) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          (dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R)) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), (∫⁻ t in Ico (0 : ℝ) ε, Δ (WithLp.toLp 2 (((l : Fin (n + 1) → ℝ) + offset) + t • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ))))) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          ∫⁻ y in ball z R, ENNReal.ofReal (‖u y - v y‖ ^ 2) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.ClosedTargetGridJoint.result hR hu hv hN huN hvN S hS a b hab hrect hε
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
