module

public import Mathlib.MeasureTheory.Measure.Restrict

public section

open MeasureTheory Set Filter

namespace StratificationTheory.Compactness

/-- A countable family of actual functions that agrees almost everywhere on
its earlier measurable regions has one ambient function agreeing with every
member on its corresponding region. -/
theorem exists_ae_glue_countable_regions {α E : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : ℕ → Set α) (hK : ∀ j, MeasurableSet (K j))
    (v : ℕ → α → E)
    (hconsistent : ∀ j k, j ≤ k → v j =ᵐ[μ.restrict (K j)] v k) :
    ∃ u : α → E, ∀ j, u =ᵐ[μ.restrict (K j)] v j := by
  classical
  let u : α → E := fun x => if hx : ∃ j, x ∈ K j then v (Nat.find hx) x else v 0 x
  refine ⟨u, ?_⟩
  intro j
  have hall : ∀ᵐ x ∂μ, ∀ n, n ≤ j → x ∈ K n → v n x = v j x := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : n ≤ j
    · have hae := (ae_restrict_iff' (hK n)).mp (hconsistent n j hn)
      exact hae.mono fun x hx _h => hx
    · exact Eventually.of_forall fun _ h => False.elim (hn h)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (hK j)] with x hx hmem
  have hex : ∃ n, x ∈ K n := ⟨j, hmem⟩
  simp only [u, dif_pos hex]
  exact hx _ (Nat.find_min' hex hmem) (Nat.find_spec hex)

end StratificationTheory.Compactness
