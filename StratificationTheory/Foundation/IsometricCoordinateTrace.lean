module

public import StratificationTheory.Frozen.CoordinateTraceJoint
public import StratificationTheory.Foundation.IsometricSobolevPullback

/-!
# Actual Sobolev traces in orthogonal coordinates

The original ball Sobolev pair is pulled back by a centered Euclidean
isometry. The coordinate trace theorem then gives the original rotated
slices, their displayed tangential weak columns and matching cut traces.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

/-- Orthogonal coordinates give the actual flat slice weak columns and
matching L2 traces of the original map in that frame. -/
theorem isometric_coordinate_flat_trace_and_cut_compatibility {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    (Q : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1)) (U : OpenDomain n)
    {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ U.val, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R) :
    let u' : Domain (n + 1) → Ambient q := fun x => u (z + Q (x - z))
    let D' : Domain (n + 1) → Gradient (n + 1) q := fun x i =>
      ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j • Du (z + Q (x - z)) j
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ := (volume : Measure (Domain n)).restrict U.val
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp
          (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ᵐ c ∂volume, ∀ hc : c ∈ Ioo a b,
        ∃ hface : MemW12 U
          (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) c)))
          (fun x i => D' (e.symm (x, EuclideanSpace.single (0 : Fin 1) c)) (Fin.castAdd 1 i)),
      ∃ L : C(Icc a c, Lp (Ambient q) 2 σ), ∃ R : C(Icc c b, Lp (Ambient q) 2 σ),
        (∀ t : Icc a c, L t = H ⟨t.val, t.property.1, t.property.2.trans hc.2.le⟩) ∧
        (∀ t : Icc c b, R t = H ⟨t.val, hc.1.le.trans t.property.1, t.property.2⟩) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hslice : MemLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
            L ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
          ∃ hslice : MemLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
            R ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        L ⟨c, hc.1.le, le_rfl⟩ = hface.2.1.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) ∧
        R ⟨c, le_rfl, hc.2.le⟩ = hface.2.1.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) c))) ∧
        (∀ K : C(Icc a c, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
            ∃ hslice : MemLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = L) ∧
        ∀ K : C(Icc c b, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
            ∃ hslice : MemLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => u' (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = R := by
  intro u' D' e σ
  exact coordinate_flat_trace_and_cut_compatibility hR
    (memW12_ball_centered_isometry hR hu Q) U hab hrect

end StratificationTheory
