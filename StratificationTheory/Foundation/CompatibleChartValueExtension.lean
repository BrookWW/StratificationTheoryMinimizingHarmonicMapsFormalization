module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Basic

public section

namespace StratificationTheory

/-- Pointwise compatible values on actual parameterized carriers have one
ambient representative. The assertion prescribes its values exactly on
those carriers and imposes no condition away from them. -/
theorem exists_ambient_representative_of_compatible_charts
    {I X Y E : Type*} [Nonempty I] [Nonempty X]
    (U : I → Set X) (chart : I → X → Y) (f : I → X → E)
    (hCompat : ∀ (i j : I) (x : X), x ∈ U i → ∀ (z : X), z ∈ U j →
      chart i x = chart j z → f i x = f j z) :
    ∃ G : Y → E, ∀ (i : I) (x : X), x ∈ U i → G (chart i x) = f i x := by
  classical
  let R := fun y : Y => ∃ i : I, ∃ x ∈ U i, chart i x = y
  let G := fun y : Y => if h : R y then f h.choose h.choose_spec.choose
    else f (Classical.arbitrary I) (Classical.arbitrary X)
  refine ⟨G, ?_⟩
  intro i x hx
  have hR : R (chart i x) := ⟨i, x, hx, rfl⟩
  dsimp only [G]
  rw [dif_pos hR]
  exact hCompat hR.choose i hR.choose_spec.choose hR.choose_spec.choose_spec.1 x hx
    hR.choose_spec.choose_spec.2

end StratificationTheory
