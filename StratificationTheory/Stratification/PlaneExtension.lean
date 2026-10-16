module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import HarmonicMaps.Sobolev

/-!
# Subspace extension

Finite-dimensional subspaces extend to planes of any admissible dimension.
The extension is an existence witness; no canonical plane is selected.
-/

public section

open Submodule Module

namespace StratificationTheory

theorem exists_submodule_extension_finrank {K E : Type*} [DivisionRing K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (V : Submodule K E) {j : ℕ}
    (hV : finrank K V ≤ j) (hj : j ≤ finrank K E) :
    ∃ W : Submodule K E, V ≤ W ∧ finrank K W = j := by
  classical
  obtain ⟨C, hC⟩ := V.exists_isCompl
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  have hsmall : j - finrank K V ≤ finrank K C := by omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := C) hsmall
  let U : Submodule K C := span K (Set.range f)
  let U' : Submodule K E := U.map C.subtype
  have hU' : U' ≤ C := Submodule.map_subtype_le C U
  have hdisjoint : Disjoint V U' := hC.disjoint.mono_right hU'
  have hUdim : finrank K U' = j - finrank K V := by
    rw [Submodule.finrank_map_subtype_eq]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hf
  refine ⟨V ⊔ U', le_sup_left, ?_⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V U'
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hsup
  rw [hsup, hUdim]
  exact Nat.add_sub_of_le hV

theorem exists_plane_containing_subspace {n : ℕ}
    (V : Submodule ℝ (HarmonicMaps.Domain n)) {j : ℕ}
    (hV : finrank ℝ V ≤ j) (hj : j ≤ n) :
    ∃ W : Submodule ℝ (HarmonicMaps.Domain n), V ≤ W ∧ finrank ℝ W = j := by
  apply exists_submodule_extension_finrank V hV
  simpa only [HarmonicMaps.Domain, finrank_euclideanSpace, Fintype.card_fin] using hj

end StratificationTheory
