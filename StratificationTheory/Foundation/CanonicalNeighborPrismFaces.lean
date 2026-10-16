module

public import StratificationTheory.Foundation.PhysicalCellIndexCoherence
public import StratificationTheory.Foundation.CubicalSignedPermutations
public import Mathlib.Data.Fin.Tuple.Basic

public section
open HarmonicMaps Set
namespace StratificationTheory

/-- Adjacent actual parent cells inherit the same global lower-cell index
and the same native prism frame. Their shared boundary maps therefore agree
as whole functions before passing to native trace classes. -/
theorem canonical_neighbor_prism_face_maps_eq {N q : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (c.val.1 : Fin r → Fin N)}
    ∀ (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Equiv.Perm (Fin (r + 1))),
    (∀ r c i side, (child r c i side).val.val.1 = i.succAboveEmb.trans c.val.val.1) →
    (∀ r c i side, (child r c i side).val.val.2 = c.val.val.2 +
      (if side then ε else 0) • EuclideanSpace.single (c.val.val.1 i) (1 : ℝ)) →
    (∀ r c i side, frame r c i side i = Fin.last r) →
    (∀ r c i side (a : Fin r), frame r c i side (i.succAbove a) = a.castSucc) →
    ∀ {r : ℕ} (p p' : Cell (r + 1)) (i : Fin (r + 1))
      (_hpAxes : p.val.val.1 = p'.val.val.1)
      (_hpOrigin : p'.val.val.2 = p.val.val.2 + ε • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ))
      (V : Cell r → Domain (r + 1) → Ambient q),
      child r p i true = child r p' i false ∧
      frame r p i true = frame r p' i false ∧
      V (child r p i true) ∘ (cubicalSignedPermutation (r + 1) (frame r p i true) (fun _ => true)) =
        V (child r p' i false) ∘ (cubicalSignedPermutation (r + 1) (frame r p' i false) (fun _ => true)) := by
  intro Cell child frame hAxes hOrigin hTime hSpatial r p p' i hpAxes hpOrigin V
  have hChild : child r p i true = child r p' i false := by
    apply Subtype.ext
    apply original_physical_cell_index_eq grid offset ε
    · rw [hAxes, hAxes, hpAxes]
    · rw [hOrigin, hOrigin, hpOrigin]
      simp only [Bool.false_eq_true, ite_true, ite_false, zero_smul, add_zero]
  have hFrame : frame r p i true = frame r p' i false := by
    apply Equiv.ext
    intro j
    refine Fin.succAboveCases i ?_ (fun a => ?_) j
    · exact (hTime r p i true).trans (hTime r p' i false).symm
    · exact (hSpatial r p i true a).trans (hSpatial r p' i false a).symm
  exact ⟨hChild, hFrame, by rw [hChild, hFrame]⟩

end StratificationTheory
