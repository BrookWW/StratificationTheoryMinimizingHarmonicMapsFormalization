-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra

import StratificationTheory.Providers.CoordinateTraceJoint

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

theorem coordinate_flat_trace_and_cut_compatibility {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (U : OpenDomain n)
    {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ U.val, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ := (volume : Measure (Domain n)).restrict U.val
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp
          (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ᵐ c ∂volume, ∀ hc : c ∈ Ioo a b,
        ∃ hface : MemW12 U
          (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c)))
          (fun x i => Du (e.symm (x, EuclideanSpace.single (0 : Fin 1) c)) (Fin.castAdd 1 i)),
      ∃ L : C(Icc a c, Lp (Ambient q) 2 σ), ∃ R : C(Icc c b, Lp (Ambient q) 2 σ),
        (∀ t : Icc a c, L t = H ⟨t.val, t.property.1, t.property.2.trans hc.2.le⟩) ∧
        (∀ t : Icc c b, R t = H ⟨t.val, hc.1.le.trans t.property.1, t.property.2⟩) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
            L ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
          ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
            R ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        L ⟨c, hc.1.le, le_rfl⟩ = hface.2.1.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) ∧
        R ⟨c, le_rfl, hc.2.le⟩ = hface.2.1.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) ∧
        (∀ K : C(Icc a c, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
            ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = L) ∧
        ∀ K : C(Icc c b, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
            ∃ hslice : MemLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = R :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.CoordinateTraceJoint.result hR hu U hab hrect
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
