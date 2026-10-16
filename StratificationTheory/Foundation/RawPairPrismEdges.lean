module

public import StratificationTheory.Foundation.CubicalThreeDimensionalIncidence

/-!
# The twelve original raw edges of a square prism

The raw affine interpolation of the two original square maps is one common
representative of all lower prism edges. Horizontal edge values are the
original source edge maps; vertical edge values are the original vertex
chords. These identities are pointwise and do not assert a prism weak graph.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The six literal signed-face/coordinate incidences all restrict the
same raw affine prism map to the original horizontal edges or vertex
chords. The coordinate directions may lie in any ambient source dimension. -/
theorem raw_pair_prism_twelve_edge_formulas {N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (u : Fin 2 → Domain N → Ambient q) (y v₀ v₁ : Domain N) :
    let δ := fun b : Bool => if b then ε else 0
    let σ := fun b : Bool => if b then (1 : ℝ) else -1
    let τ := fun s : ℝ => ε / 2 + (ε / 2) * s
    let U := fun (l : Fin 2) (x : Domain 2) => u l (y + τ (x 0) • v₀ + τ (x 1) • v₁)
    let E := fun z : Domain 3 =>
      (1 - (z 2 + 1) / 2) • U 0 (WithLp.toLp 2 ![z 0, z 1]) +
        ((z 2 + 1) / 2) • U 1 (WithLp.toLp 2 ![z 0, z 1])
    let edge₀ := fun (b c : Bool) (x : Domain 1) =>
      u (if c then 1 else 0) ((y + δ b • v₀) + τ (x 0) • v₁)
    let edge₁ := fun (b c : Bool) (x : Domain 1) =>
      u (if c then 1 else 0) ((y + δ b • v₁) + τ (x 0) • v₀)
    let chord₀ := fun (b c : Bool) (x : Domain 1) =>
      (1 - τ (x 0) / ε) • u 0 ((y + δ b • v₀) + δ c • v₁) +
        (τ (x 0) / ε) • u 1 ((y + δ b • v₀) + δ c • v₁)
    let chord₁ := fun (b c : Bool) (x : Domain 1) =>
      (1 - τ (x 0) / ε) • u 0 ((y + δ b • v₁) + δ c • v₀) +
        (τ (x 0) / ε) • u 1 ((y + δ b • v₁) + δ c • v₀)
    ∀ (b c : Bool) (x : Domain 1),
      E (WithLp.toLp 2 ![σ b, x 0, σ c]) = edge₀ b c x ∧
      E (WithLp.toLp 2 ![σ b, σ c, x 0]) = chord₀ b c x ∧
      E (WithLp.toLp 2 ![σ c, σ b, x 0]) = chord₁ b c x ∧
      E (WithLp.toLp 2 ![x 0, σ b, σ c]) = edge₁ b c x ∧
      E (WithLp.toLp 2 ![σ c, x 0, σ b]) =
        U (if b then 1 else 0) (WithLp.toLp 2 ![σ c, x 0]) ∧
      E (WithLp.toLp 2 ![x 0, σ c, σ b]) =
        U (if b then 1 else 0) (WithLp.toLp 2 ![x 0, σ c]) := by
  intro δ σ τ U E edge₀ edge₁ chord₀ chord₁ b c x
  have hτsign (b : Bool) : τ (σ b) = δ b := by
    cases b <;> dsimp [τ, σ, δ] <;> ring
  have hτdiv (s : ℝ) : τ s / ε = (s + 1) / 2 := by
    dsimp [τ]
    field_simp [hε.ne']
    ring
  have hp₁ (b : Bool) (s : ℝ) :
      y + τ s • v₀ + τ (σ b) • v₁ = (y + δ b • v₁) + τ s • v₀ := by
    rw [hτsign]
    abel
  have hp₀ (b : Bool) (s : ℝ) :
      y + τ (σ b) • v₀ + τ s • v₁ = (y + δ b • v₀) + τ s • v₁ := by
    rw [hτsign]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases c <;> simp [E, U, edge₀, σ, hp₀]
  · simp [E, U, chord₀, hτsign, hτdiv]
  · have hp : y + δ c • v₀ + δ b • v₁ = y + δ b • v₁ + δ c • v₀ := by abel
    simp [E, U, chord₁, hτsign, hτdiv, hp]
  · cases c <;> simp [E, U, edge₁, σ, hp₁]
  · cases b <;> simp [E, σ]
  · cases b <;> simp [E, σ]

end StratificationTheory
