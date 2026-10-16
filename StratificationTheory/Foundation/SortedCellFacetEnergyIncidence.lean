module
public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier
public import Mathlib.Order.WellFounded
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Fin.SuccPred

/-!
# Actual finite incidence of sorted physical cell facets

A child cell, its removed ambient coordinate and its signed side recover
the original sorted parent cell and facet. This bounds the full original
facet energy sum by a dimension-only multiplicity of the lower-cell sum.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

private theorem coordinate_embedding_range_insert_deleted {k N : ℕ}
    (c : Fin (k + 1) ↪ Fin N) (i : Fin (k + 1)) :
    Set.range c = insert (c i) (Set.range (i.succAboveEmb.trans c)) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j = i
    · exact Or.inl (congrArg c hj)
    · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hj
      exact Or.inr ⟨a, congrArg c ha⟩
  · rintro (hx | ⟨a, ha⟩)
    · exact ⟨i, hx.symm⟩
    · exact ⟨i.succAbove a, ha⟩

/-- A sorted parent coordinate embedding is determined by its actual
removed normal and its original increasing lower-facet embedding. -/
theorem sorted_coordinate_embedding_eq_of_deleted_eq {k N : ℕ}
    (c d : Fin (k + 1) ↪ Fin N) (hc : StrictMono (c : Fin (k + 1) → Fin N))
    (hd : StrictMono (d : Fin (k + 1) → Fin N)) (i j : Fin (k + 1))
    (hNormal : c i = d j) (hDeleted : i.succAboveEmb.trans c = j.succAboveEmb.trans d) : c = d := by
  have hRange : Set.range c = Set.range d := by
    rw [coordinate_embedding_range_insert_deleted c i,
      coordinate_embedding_range_insert_deleted d j, hNormal, hDeleted]
  exact Function.Embedding.ext (congrFun ((hc.range_inj hd).mp hRange))

/-- The actual original sorted parent facet index is injectively recovered
from its removed ambient normal, signed side and original lower-cell key. -/
theorem sorted_physical_cell_facet_incidence_injective {k N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    ∀ child : Cell (k + 1) → Fin (k + 1) → Bool → Cell k,
    (∀ p i side, (child p i side).val.val.1 = i.succAboveEmb.trans p.val.val.1) →
    (∀ p i side, (child p i side).val.val.2 =
      p.val.val.2 + (if side then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ)) →
    Function.Injective (fun t : Cell (k + 1) × (Fin (k + 1) × Bool) =>
      ((t.1.val.val.1 t.2.1, t.2.2), child t.1 t.2.1 t.2.2)) := by
  intro Cell child hAxes hOrigin
  rintro ⟨p, i, side⟩ ⟨q, j, side'⟩ h
  have hNormal : p.val.val.1 i = q.val.val.1 j := congrArg (fun a => a.1.1) h
  have hSide : side = side' := congrArg (fun a => a.1.2) h
  have hChild : child p i side = child q j side' := congrArg Prod.snd h
  have hDeleted : i.succAboveEmb.trans p.val.val.1 = j.succAboveEmb.trans q.val.val.1 := by
    rw [← hAxes p i side, ← hAxes q j side']
    exact congrArg (fun a : Cell k => a.val.val.1) hChild
  have hParentAxes : p.val.val.1 = q.val.val.1 :=
    sorted_coordinate_embedding_eq_of_deleted_eq p.val.val.1 q.val.val.1 p.property q.property
      i j hNormal hDeleted
  have hShift : p.val.val.2 + (if side then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ) =
      q.val.val.2 + (if side' then ε else 0) • EuclideanSpace.single (q.val.val.1 j) (1 : ℝ) := by
    rw [← hOrigin p i side, ← hOrigin q j side']
    exact congrArg (fun a : Cell k => a.val.val.2) hChild
  rw [hSide, hNormal] at hShift
  have hParentOrigin : p.val.val.2 = q.val.val.2 := add_right_cancel hShift
  have hp : p = q := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hParentAxes hParentOrigin
  have hij : i = j := p.val.val.1.injective (by simpa only [hParentAxes] using hNormal)
  subst q
  subst j
  subst side'
  rfl

/-- Actual sorted lower-cell energies occur in the full parent facet sum
at most twice the ambient dimension, independently of the number of cells. -/
theorem tsum_sorted_physical_cell_facet_energy_le {k N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    ∀ child : Cell (k + 1) → Fin (k + 1) → Bool → Cell k,
    (∀ p i side, (child p i side).val.val.1 = i.succAboveEmb.trans p.val.val.1) →
    (∀ p i side, (child p i side).val.val.2 =
      p.val.val.2 + (if side then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ)) →
    ∀ E : Cell k → ℝ≥0∞,
      (∑' p : Cell (k + 1), ∑ i : Fin (k + 1), ∑ side : Bool, E (child p i side)) ≤
        (2 * (N : ℝ≥0∞)) * ∑' c : Cell k, E c := by
  intro Cell child hAxes hOrigin E
  let f : Cell (k + 1) × (Fin (k + 1) × Bool) → (Fin N × Bool) × Cell k :=
    fun t => ((t.1.val.val.1 t.2.1, t.2.2), child t.1 t.2.1 t.2.2)
  have hf : Function.Injective f := sorted_physical_cell_facet_incidence_injective grid offset ε child hAxes hOrigin
  have hSum := ENNReal.tsum_comp_le_tsum_of_injective hf (fun t : (Fin N × Bool) × Cell k => E t.2)
  calc
    _ = ∑' t : Cell (k + 1) × (Fin (k + 1) × Bool), E (child t.1 t.2.1 t.2.2) := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro p
      rw [ENNReal.tsum_prod']
      simp only [tsum_fintype]
    _ ≤ ∑' t : (Fin N × Bool) × Cell k, E t.2 := hSum
    _ = _ := by
      rw [ENNReal.tsum_prod']
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring

end StratificationTheory
