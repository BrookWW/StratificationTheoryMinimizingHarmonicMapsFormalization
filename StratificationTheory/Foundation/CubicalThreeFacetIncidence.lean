module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import Mathlib.Data.Fin.Embedding

public section

open HarmonicMaps

namespace StratificationTheory

/-- Distinct canonical square facets of an actual coordinate three-cell
have local normal indices that select each other's normal coordinate and
retain the same original oriented edge coordinate. -/
theorem cubical_three_facet_shared_edge_indices {N : ℕ}
    (coord : Fin 3 ↪ Fin N) (i j : Fin 3) (hij : i ≠ j) :
    let pair : Fin 3 → (Fin 2 ↪ Fin N) := fun k =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) k).toEmbedding).trans coord
    let other := Equiv.swap (0 : Fin 2) 1
    ∃ a b : Fin 2, pair i a = coord j ∧ pair j b = coord i ∧
      pair i (other a) = pair j (other b) := by
  intro pair other
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  · exact ⟨1, 0, by simp [pair, Fin.last]; decide,
      by simp [pair, Fin.last]; decide,
      by simp [pair, other, Fin.last]⟩
  · exact ⟨0, 0, by simp [pair, Fin.last],
      by simp [pair, Fin.last],
      by simp [pair, other, Fin.last]; decide⟩
  · exact ⟨0, 1, by simp [pair, Fin.last]; decide,
      by simp [pair, Fin.last]; decide,
      by simp [pair, other, Fin.last]⟩
  · exact ⟨1, 1, by simp [pair, Fin.last],
      by simp [pair, Fin.last],
      by simp [pair, other, Fin.last]; decide⟩
  · exact ⟨0, 0, by simp [pair, Fin.last],
      by simp [pair, Fin.last],
      by simp [pair, other, Fin.last]; decide⟩
  · exact ⟨1, 1, by simp [pair, Fin.last],
      by simp [pair, Fin.last],
      by simp [pair, other, Fin.last]; decide⟩

/-- The corresponding two physical edge origins agree on every signed
pair of original three-cell facets. -/
theorem cubical_three_facet_shared_edge_origins {N : ℕ}
    (coord : Fin 3 ↪ Fin N) (ε : ℝ) (y : Domain N)
    (i j : Fin 3) (sideI sideJ : Bool) (hij : i ≠ j) :
    let pair : Fin 3 → (Fin 2 ↪ Fin N) := fun k =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) k).toEmbedding).trans coord
    let δ := fun side : Bool => if side then ε else 0
    let origin := fun k side => y + δ side • EuclideanSpace.single (coord k) (1 : ℝ)
    let other := Equiv.swap (0 : Fin 2) 1
    ∃ a b : Fin 2, pair i a = coord j ∧ pair j b = coord i ∧
      pair i (other a) = pair j (other b) ∧
      origin i sideI + δ sideJ • EuclideanSpace.single (pair i a) (1 : ℝ) =
        origin j sideJ + δ sideI • EuclideanSpace.single (pair j b) (1 : ℝ) := by
  intro pair δ origin other
  obtain ⟨a, b, ha, hb, hT⟩ := cubical_three_facet_shared_edge_indices coord i j hij
  refine ⟨a, b, ha, hb, hT, ?_⟩
  rw [ha, hb]
  dsimp only [origin]
  abel

end StratificationTheory
