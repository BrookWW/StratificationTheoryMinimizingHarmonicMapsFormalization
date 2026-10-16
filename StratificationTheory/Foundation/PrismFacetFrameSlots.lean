module

public import StratificationTheory.Foundation.PrismFacetCoordinates

public section

namespace StratificationTheory

/-- Canonical native frame slots recover the actual parent physical normal
of every lower trace. The time and spatial cases use the same finite frame
and the actual outer face exchange. -/
theorem prism_facet_frame_slot_characterization {d : ℕ}
    (i : Fin (d + 1)) (p : Equiv.Perm (Fin (d + 1)))
    (hTime : p i = Fin.last d)
    (hSpatial : ∀ a : Fin d, p (i.succAbove a) = a.castSucc) (j : Fin (d + 1)) :
    (p j = Fin.last d ↔
      (Equiv.swap (Fin.last (d + 1)) i.castSucc) j.castSucc = Fin.last (d + 1)) ∧
    ∀ a : Fin d, p j = a.castSucc ↔
      (Equiv.swap (Fin.last (d + 1)) i.castSucc) j.castSucc = (i.succAbove a).castSucc := by
  let σ := Equiv.swap (Fin.last (d + 1)) i.castSucc
  have hNormalTime : σ j.castSucc = Fin.last (d + 1) ↔ j = i := by
    constructor
    · intro h
      apply Fin.castSucc_injective
      apply σ.injective
      exact h.trans (Equiv.swap_apply_right (Fin.last (d + 1)) i.castSucc).symm
    · rintro rfl
      exact Equiv.swap_apply_right _ _
  have hNormalSpatial (a : Fin d) : σ j.castSucc = (i.succAbove a).castSucc ↔ j = i.succAbove a := by
    have hFix : σ (i.succAbove a).castSucc = (i.succAbove a).castSucc :=
      Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last _)
        (fun h => Fin.succAbove_ne i a (Fin.castSucc_injective _ h))
    constructor
    · intro h
      exact Fin.castSucc_injective _ (σ.injective (h.trans hFix.symm))
    · rintro rfl
      exact hFix
  constructor
  · rw [hNormalTime]
    exact ⟨fun h => p.injective (h.trans hTime.symm), fun h => h ▸ hTime⟩
  · intro a
    rw [hNormalSpatial]
    exact ⟨fun h => p.injective (h.trans (hSpatial a).symm), fun h => h ▸ hSpatial a⟩

end StratificationTheory
