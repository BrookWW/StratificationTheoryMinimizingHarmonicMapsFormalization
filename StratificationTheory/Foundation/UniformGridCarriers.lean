module

public import HarmonicMaps.Sobolev
public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- The actual open physical cell of the finite uniform coordinate mesh. -/
@[expose] noncomputable def uniformGridCell (d N : ℕ) (ε : ℝ) (z : Fin d → Fin N) : OpenDomain d :=
  ⟨⋂ i : Fin d, (EuclideanSpace.proj i) ⁻¹' Ioo ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε),
    isOpen_iInter_of_finite (fun i : Fin d =>
      isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩

/-- The entire positive open box occupied by the finite uniform mesh. -/
@[expose] noncomputable def uniformGridBox (d N : ℕ) (ε : ℝ) : OpenDomain d :=
  ⟨⋂ i : Fin d, (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) ((N : ℝ) * ε),
    isOpen_iInter_of_finite (fun i : Fin d =>
      isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩

/-- The actual native transverse face box of one physical mesh cell in the
positive coordinate-normal face chart. -/
@[expose] noncomputable def uniformGridTransverseCell (n N : ℕ) (ε : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) : OpenDomain n :=
  ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹'
      Ioo ((z ((Equiv.swap (Fin.last n) i) k.castSucc)).val * ε)
        (((z ((Equiv.swap (Fin.last n) i) k.castSucc)).val + (1 : ℝ)) * ε),
    isOpen_iInter_of_finite (fun k : Fin n =>
      isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩

/-- Complete membership characterization on the whole original cell carrier. -/
theorem mem_uniformGridCell_iff (d N : ℕ) (ε : ℝ) (z : Fin d → Fin N) (x : Domain d) :
    x ∈ (uniformGridCell d N ε z).val ↔ ∀ i : Fin d,
      x i ∈ Ioo ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε) := by
  simp only [uniformGridCell, mem_iInter, mem_preimage]
  rfl

/-- Complete membership characterization on the whole original mesh box. -/
theorem mem_uniformGridBox_iff (d N : ℕ) (ε : ℝ) (x : Domain d) :
    x ∈ (uniformGridBox d N ε).val ↔ ∀ i : Fin d, x i ∈ Ioo (0 : ℝ) ((N : ℝ) * ε) := by
  simp only [uniformGridBox, mem_iInter, mem_preimage]
  rfl

/-- Complete membership characterization on the whole native transverse box. -/
theorem mem_uniformGridTransverseCell_iff (n N : ℕ) (ε : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (x : Domain n) :
    x ∈ (uniformGridTransverseCell n N ε i z).val ↔ ∀ k : Fin n,
      x k ∈ Ioo ((z ((Equiv.swap (Fin.last n) i) k.castSucc)).val * ε)
        (((z ((Equiv.swap (Fin.last n) i) k.castSucc)).val + (1 : ℝ)) * ε) := by
  simp only [uniformGridTransverseCell, mem_iInter, mem_preimage]
  rfl

end StratificationTheory
