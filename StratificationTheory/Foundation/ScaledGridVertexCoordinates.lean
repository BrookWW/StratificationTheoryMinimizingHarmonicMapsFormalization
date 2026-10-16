module
public import StratificationTheory.Foundation.GridNeighborCoordinates
public import StratificationTheory.Foundation.CubicalVertexEdgeCoverage

/-!
# Actual integer coordinates and vertices of a scaled selected grid

Differences of points of the same selected grid have integer multiples of
the physical mesh size as coordinates. A genuine edge inside one closed
mesh cube therefore starts at an actual vertex with zero tangent offset.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Every coordinate of an actual element of the scaled integer lattice is
an integer multiple of the original mesh length. -/
theorem scaled_grid_span_coordinate_integer {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    let grid := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _ : Fin N => ε) (fun _ => hε.ne'.isUnit)
    ∀ (z : Submodule.span ℤ (Set.range grid)) (j : Fin N),
      ∃ k : ℤ, (z : Fin N → ℝ) j = (k : ℝ) * ε := by
  intro grid z j
  have h : ∀ (x : Fin N → ℝ), x ∈ Submodule.span ℤ (Set.range grid) →
      ∃ k : ℤ, x j = (k : ℝ) * ε := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        by_cases hi : j = i
        · subst j
          refine ⟨1, ?_⟩
          simp only [grid, Basis.isUnitSMul_apply, Pi.basisFun_apply,
            Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Int.cast_one, one_mul]
        · refine ⟨0, ?_⟩
          simp only [grid, Basis.isUnitSMul_apply, Pi.basisFun_apply,
            Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero, Int.cast_zero, zero_mul]
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨kx, hkx⟩ := ihx
        obtain ⟨ky, hky⟩ := ihy
        refine ⟨kx + ky, ?_⟩
        change x j + y j = _
        rw [hkx, hky, Int.cast_add]
        ring
    | smul a x hx ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨a * k, ?_⟩
        change a • x j = _
        rw [zsmul_eq_mul, hk, Int.cast_mul]
        ring
  exact h z z.property

/-- A mesh multiple lying between zero and one mesh length is exactly one
of the two physical vertex displacements. -/
theorem scaled_integer_between_zero_mesh {ε t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc (0 : ℝ) ε) (hInteger : ∃ k : ℤ, t = (k : ℝ) * ε) :
    t = 0 ∨ t = ε := by
  obtain ⟨k, rfl⟩ := hInteger
  have hk₀ : (0 : ℝ) ≤ (k : ℝ) := by nlinarith [ht.1]
  have hk₁ : (k : ℝ) ≤ 1 := by nlinarith [ht.2]
  have hk₀' : (0 : ℤ) ≤ k := by exact_mod_cast hk₀
  have hk₁' : k ≤ (1 : ℤ) := by exact_mod_cast hk₁
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl <;> simp

/-- Any actual same-grid edge contained in a closed parent mesh cube has
the original parent-vertex displacements and zero tangent displacement. -/
theorem scaled_grid_contained_edge_vertex_coordinates {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (offset : Fin N → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _ : Fin N => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin N → ℝ) + offset)
    ∀ (parent edge : L) (normal : Fin N),
      (∀ s ∈ Icc (0 : ℝ) ε, ∀ j,
        (y edge + s • EuclideanSpace.single normal (1 : ℝ)) j - (y parent) j ∈ Icc (0 : ℝ) ε) →
      y edge normal = y parent normal ∧
      (∀ j, y edge j - y parent j = 0 ∨ y edge j - y parent j = ε) := by
  intro grid L y parent edge normal hClosed
  have h₀ (j : Fin N) : y edge j - y parent j ∈ Icc (0 : ℝ) ε := by
    simpa only [zero_smul, add_zero] using hClosed 0 ⟨le_rfl, hε.le⟩ j
  have hεn := hClosed ε ⟨hε.le, le_rfl⟩ normal
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
    smul_eq_mul, mul_one] at hεn
  refine ⟨by linarith [(h₀ normal).1, hεn.2], ?_⟩
  intro j
  apply scaled_integer_between_zero_mesh hε (h₀ j)
  obtain ⟨k, hk⟩ := scaled_grid_span_coordinate_integer hε (edge - parent) j
  refine ⟨k, ?_⟩
  change ((edge : Fin N → ℝ) j + offset j) - ((parent : Fin N → ℝ) j + offset j) = _
  change ((edge : Fin N → ℝ) j - (parent : Fin N → ℝ) j) = _ at hk
  linarith only [hk]

end StratificationTheory
