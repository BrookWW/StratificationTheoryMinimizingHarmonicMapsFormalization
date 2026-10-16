module

public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier
public import StratificationTheory.Foundation.CanonicalCellDoubleDeletion
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

public section

open HarmonicMaps MeasureTheory Set Filter

namespace StratificationTheory

/-- Physical coordinate-cell indices agree once the ordered coordinates
and original physical origins agree. Lattice witnesses introduce no extra
choice into the index. -/
theorem original_physical_cell_index_eq {k N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (p₀ p₁ : originalPhysicalCellCarrier k grid offset ε)
    (hc : p₀.val.1 = p₁.val.1) (hy : p₀.val.2 = p₁.val.2) : p₀ = p₁ :=
  Subtype.ext (Prod.ext hc hy)

/-- Canonical double-deletion facets use the same global lower-cell
index, in either order of deleting the two actual spatial normals. -/
theorem canonical_double_deleted_physical_cell_index_eq {k N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (c : Fin (k + 2) ↪o Fin N) (y : Domain N) (i : Fin (k + 2)) (a : Fin (k + 1))
    (sideI sideJ : Bool) (p₀ p₁ : originalPhysicalCellCarrier k grid offset ε) :
    let j := i.succAbove a
    let b := a.predAbove i
    let c₀ := (Fin.succAboveOrderEmb i).trans c
    let c₁ := (Fin.succAboveOrderEmb j).trans c
    let d₀ := (Fin.succAboveOrderEmb a).trans c₀
    let d₁ := (Fin.succAboveOrderEmb b).trans c₁
    let δ := fun side : Bool => if side then ε else 0
    p₀.val.1 = d₀.toEmbedding → p₁.val.1 = d₁.toEmbedding →
    p₀.val.2 = (y + δ sideI • EuclideanSpace.single (c i) (1 : ℝ)) +
      δ sideJ • EuclideanSpace.single (c₀ a) (1 : ℝ) →
    p₁.val.2 = (y + δ sideJ • EuclideanSpace.single (c j) (1 : ℝ)) +
      δ sideI • EuclideanSpace.single (c₁ b) (1 : ℝ) → p₀ = p₁ := by
  intro j b c₀ c₁ d₀ d₁ δ hc₀ hc₁ hy₀ hy₁
  have h := canonical_cell_double_deletion c i a ε y
  apply original_physical_cell_index_eq grid offset ε p₀ p₁
  · rw [hc₀, hc₁]
    exact congrArg (fun d : Fin k ↪o Fin N => d.toEmbedding) h.1
  · rw [hy₀, hy₁]
    exact (h.2.2.2 sideI sideJ).1

/-- Actual original endpoint classes through the same global physical
cell and the same native chart are equal as native L2 objects. -/
theorem lp_endpoint_classes_eq_of_global_physical_cell {k N q : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (V : originalPhysicalCellCarrier k grid offset ε → Domain (k + 1) → Ambient q)
    (p₀ p₁ : originalPhysicalCellCarrier k grid offset ε) (hIndex : p₀ = p₁)
    (μ : Measure (Domain (k + 1))) (F : Domain (k + 1) → Domain (k + 1))
    (H₀ H₁ : Lp (Ambient q) 2 μ)
    (h₀ : (H₀ : Domain (k + 1) → Ambient q) =ᵐ[μ] V p₀ ∘ F)
    (h₁ : (H₁ : Domain (k + 1) → Ambient q) =ᵐ[μ] V p₁ ∘ F) : H₀ = H₁ := by
  subst p₁
  apply Lp.ext
  exact h₀.trans h₁.symm

end StratificationTheory
