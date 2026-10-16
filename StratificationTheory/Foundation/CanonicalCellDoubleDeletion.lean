module

public import HarmonicMaps.Sobolev
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.SuccPred

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- Two orders of removing the same original coordinate normals have the
same increasing lower-face embedding and the same physical origin. Thus
the entire original lower-cell parameterization agrees pointwise. -/
theorem canonical_cell_double_deletion {k N : ℕ}
    (c : Fin (k + 2) ↪o Fin N) (i : Fin (k + 2)) (a : Fin (k + 1))
    (ε : ℝ) (y : Domain N) :
    let j := i.succAbove a
    let b := a.predAbove i
    let c₀ := (Fin.succAboveOrderEmb i).trans c
    let c₁ := (Fin.succAboveOrderEmb j).trans c
    let d₀ := (Fin.succAboveOrderEmb a).trans c₀
    let d₁ := (Fin.succAboveOrderEmb b).trans c₁
    d₀ = d₁ ∧ c₀ a = c j ∧ c₁ b = c i ∧
      ∀ (sideI sideJ : Bool),
        let δ := fun side : Bool => if side then ε else 0
        let y₀ := (y + δ sideI • EuclideanSpace.single (c i) (1 : ℝ)) +
          δ sideJ • EuclideanSpace.single (c₀ a) (1 : ℝ)
        let y₁ := (y + δ sideJ • EuclideanSpace.single (c j) (1 : ℝ)) +
          δ sideI • EuclideanSpace.single (c₁ b) (1 : ℝ)
        y₀ = y₁ ∧ ∀ t : Domain k,
          y₀ + ∑ s : Fin k, t s • EuclideanSpace.single (d₀ s) (1 : ℝ) =
            y₁ + ∑ s : Fin k, t s • EuclideanSpace.single (d₁ s) (1 : ℝ) := by
  intro j b c₀ c₁ d₀ d₁
  have hDeleted : d₀ = d₁ := by
    apply DFunLike.ext
    intro s
    change c (i.succAbove (a.succAbove s)) = c ((i.succAbove a).succAbove ((a.predAbove i).succAbove s))
    exact congrArg c (Fin.succAbove_succAbove_succAbove_predAbove i a s).symm
  have hNormal₀ : c₀ a = c j := rfl
  have hNormal₁ : c₁ b = c i := by
    change c ((i.succAbove a).succAbove (a.predAbove i)) = c i
    rw [Fin.succAbove_succAbove_predAbove]
  refine ⟨hDeleted, hNormal₀, hNormal₁, ?_⟩
  intro sideI sideJ δ y₀ y₁
  have hOrigin : y₀ = y₁ := by
    dsimp only [y₀, y₁]
    rw [hNormal₀, hNormal₁]
    abel
  refine ⟨hOrigin, ?_⟩
  intro t
  rw [hOrigin, hDeleted]

end StratificationTheory
