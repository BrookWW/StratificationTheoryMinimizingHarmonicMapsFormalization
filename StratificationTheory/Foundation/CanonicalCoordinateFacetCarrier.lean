module

public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Fin.Basic

public section

open HarmonicMaps Set
open scoped BigOperators

namespace StratificationTheory

/-- A canonical ordered deletion gives the actual original closed facet,
with the exact shifted physical origin and no reordering of its parameters. -/
theorem canonical_coordinate_cell_closed_facet_containment {d N : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (coord : Fin (d + 1) ↪ Fin N) (y : Domain N)
    (hCell : ∀ t : Domain (d + 1), (∀ k, t k ∈ Icc (0 : ℝ) ε) →
      ∀ k : Fin N, (y + ∑ j, t j • EuclideanSpace.single (coord j) (1 : ℝ)) k ∈ Ioo (-1 : ℝ) 1)
    (i : Fin (d + 1)) (side : Bool) :
    let lower := (Fin.succAboveOrderEmb i).toEmbedding.trans coord
    let origin := y + (if side then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    ∀ t : Domain d, (∀ k, t k ∈ Icc (0 : ℝ) ε) →
      ∀ k : Fin N, (origin + ∑ j, t j • EuclideanSpace.single (lower j) (1 : ℝ)) k ∈ Ioo (-1 : ℝ) 1 := by
  intro lower origin t ht
  let δ : ℝ := if side then ε else 0
  let T : Domain (d + 1) := WithLp.toLp 2 (i.insertNth δ (WithLp.ofLp t))
  have hδ : δ ∈ Icc (0 : ℝ) ε := by cases side <;> simp [δ, hε]
  have hT : ∀ k, T k ∈ Icc (0 : ℝ) ε := by
    intro k
    by_cases hki : k = i
    · subst k
      change Fin.insertNth (α := fun _ => ℝ) i δ (fun a => t a) i ∈ Icc (0 : ℝ) ε
      rw [Fin.insertNth_apply_same]
      exact hδ
    · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hki
      rw [← ha]
      change Fin.insertNth (α := fun _ => ℝ) i δ (fun a => t a) (i.succAbove a) ∈ Icc (0 : ℝ) ε
      rw [Fin.insertNth_apply_succAbove]
      exact ht a
  have hPoint : y + ∑ j, T j • EuclideanSpace.single (coord j) (1 : ℝ) =
      origin + ∑ j, t j • EuclideanSpace.single (lower j) (1 : ℝ) := by
    rw [Fin.sum_univ_succAbove _ i]
    change y + (Fin.insertNth (α := fun _ => ℝ) i δ (fun a => t a) i • EuclideanSpace.single (coord i) (1 : ℝ) +
      ∑ j : Fin d, Fin.insertNth (α := fun _ => ℝ) i δ (fun a => t a) (i.succAbove j) •
        EuclideanSpace.single (coord (i.succAbove j)) (1 : ℝ)) = _
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    change y + (δ • _ + _) = (y + δ • _) + _
    exact (add_assoc _ _ _).symm
  intro k
  rw [← hPoint]
  exact hCell T hT k

/-- On the actual epsilon-coordinate lattice, every canonical facet of an
original contained physical cell is again in the same original physical
carrier, with its exact inherited coordinate embedding and physical origin. -/
theorem mem_original_physical_cell_canonical_facet {d N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hGrid : ∀ j, grid j = ε • Pi.single j (1 : ℝ))
    (p : originalPhysicalCellCarrier (d + 1) grid offset ε)
    (i : Fin (d + 1)) (side : Bool) :
    (((Fin.succAboveOrderEmb i).toEmbedding.trans p.val.1),
      p.val.2 + (if side then ε else 0) • EuclideanSpace.single (p.val.1 i) (1 : ℝ)) ∈
        originalPhysicalCellCarrier d grid offset ε := by
  obtain ⟨z, hz, hy⟩ := (mem_originalPhysicalCellCarrier_iff _ _ _ _ _).mp p.property
  let δ : ℝ := if side then ε else 0
  let v : Fin N → ℝ := δ • Pi.single (p.val.1 i) (1 : ℝ)
  have hv : v ∈ Submodule.span ℤ (Set.range grid) := by
    cases side
    · simpa only [v, δ, Bool.false_eq_true, ite_false, zero_smul] using
        (Submodule.zero_mem (Submodule.span ℤ (Set.range grid)))
    · have hg : grid (p.val.1 i) ∈ Submodule.span ℤ (Set.range grid) :=
        Submodule.subset_span ⟨p.val.1 i, rfl⟩
      change (ε • Pi.single (p.val.1 i) (1 : ℝ) : Fin N → ℝ) ∈ Submodule.span ℤ (Set.range grid)
      rw [← hGrid]
      exact hg
  let z' : Submodule.span ℤ (Set.range grid) := ⟨(z : Fin N → ℝ) + v,
    Submodule.add_mem _ z.property hv⟩
  have hy' : WithLp.toLp 2 ((z' : Fin N → ℝ) + offset) =
      p.val.2 + δ • EuclideanSpace.single (p.val.1 i) (1 : ℝ) := by
    rw [← hy]
    ext j
    change ((z : Fin N → ℝ) j + v j) + offset j =
      (((z : Fin N → ℝ) j + offset j) + δ * ((Pi.single (p.val.1 i) (1 : ℝ) : Fin N → ℝ) j))
    dsimp only [v, Pi.smul_apply, smul_eq_mul]
    ring
  apply (mem_originalPhysicalCellCarrier_iff _ _ _ _ _).mpr
  refine ⟨z', ?_, hy'⟩
  apply (mem_originalCoordinateCellCarrier_iff _ _ _ _ _).mpr
  have hClosed := (mem_originalCoordinateCellCarrier_iff _ _ _ _ _).mp hz
  rw [hy] at hClosed
  have hLower := canonical_coordinate_cell_closed_facet_containment hε p.val.1 p.val.2 hClosed i side
  rw [hy']
  exact hLower

end StratificationTheory
