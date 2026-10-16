module

public import StratificationTheory.Foundation.ThreePrismSpacetimeFacetCoordinates
public import Mathlib.Order.Fin.Basic

public section

open HarmonicMaps

namespace StratificationTheory

/-- A spatial facet of a prism uses the actual lower prism coordinates,
with the original independent time unchanged, at every normal height. -/
theorem prism_spatial_facet_coordinates {k : ℕ} (i : Fin (k + 1)) (positive : Bool)
    (z : Domain (k + 1)) (h : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 1) (m := 1)
    let A := cubicalSignedFaceIsometry k i true
    let spatial := cubicalSignedFaceIsometry k i positive
      (e.symm ((e z).1, EuclideanSpace.single (0 : Fin 1) h))
    cubicalSignedFaceIsometry (k + 1) i.castSucc positive
      (E.symm (A z, EuclideanSpace.single (0 : Fin 1) h)) =
      E.symm (spatial, (e z).2) := by
  intro e E A spatial
  have hE (v : Domain (k + 1)) (s : Domain 1) (j : Fin (k + 1)) :
      E.symm (v, s) j.castSucc = v j := by
    change (E (E.symm (v, s))).1 j = v j
    rw [E.apply_symm_apply]
  have hEt (v : Domain (k + 1)) (s : Domain 1) :
      E.symm (v, s) (Fin.last (k + 1)) = s 0 := by
    change (E (E.symm (v, s))).2 0 = s 0
    rw [E.apply_symm_apply]
  have he (v : Domain k) (s : Domain 1) (j : Fin k) :
      e.symm (v, s) j.castSucc = v j := by
    change (e (e.symm (v, s))).1 j = v j
    rw [e.apply_symm_apply]
  have het (v : Domain k) (s : Domain 1) :
      e.symm (v, s) (Fin.last k) = s 0 := by
    change (e (e.symm (v, s))).2 0 = s 0
    rw [e.apply_symm_apply]
  have hbase (j : Fin k) : (e z).1 j = z j.castSucc := rfl
  have htime : (e z).2 0 = z (Fin.last k) := rfl
  ext j
  induction j using Fin.lastCases with
  | last =>
    rw [cubicalSignedFaceIsometry_coordinate]
    simp only [Ne.symm (Fin.castSucc_ne_last i), ite_false, Equiv.swap_apply_left,
      hE, hEt, htime]
    change cubicalSignedFaceIsometry k i true z i = z (Fin.last k)
    simp only [cubicalSignedFaceIsometry_coordinate, ite_true]
  | cast j =>
    rw [cubicalSignedFaceIsometry_coordinate, hE]
    by_cases hji : j = i
    · subst j
      simp only [ite_true, hEt, PiLp.single_apply, Fin.isValue]
      dsimp only [spatial]
      simp only [cubicalSignedFaceIsometry_coordinate, ite_true, het,
        PiLp.single_apply, Fin.isValue]
    · have hcast : j.castSucc ≠ i.castSucc := by
        intro hj
        exact hji (Fin.castSucc_injective _ hj)
      have hswap : (Equiv.swap (Fin.last (k + 1)) i.castSucc) j.castSucc = j.castSucc :=
        Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last j) hcast
      rw [if_neg hcast, hswap, hE]
      dsimp only [A, spatial]
      rw [cubicalSignedFaceIsometry_coordinate, cubicalSignedFaceIsometry_coordinate,
        if_neg hji, if_neg hji]
      have hsne : (Equiv.swap (Fin.last k) i) j ≠ Fin.last k := by
        intro heq
        apply hji
        apply (Equiv.swap (Fin.last k) i).injective
        exact heq.trans (Equiv.swap_apply_right (Fin.last k) i).symm
      obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last hsne
      rw [← ha, he, hbase]

/-- The swap-based native facet chart and ordered coordinate deletion
have the same actual free coordinates, related by a finite permutation. -/
theorem exists_ordered_facet_swap_permutation {k : ℕ} (i : Fin (k + 1)) :
    ∃ r : Equiv.Perm (Fin k), ∀ j : Fin k,
      (Equiv.swap (Fin.last k) i) j.castSucc = i.succAbove (r j) := by
  classical
  let σ := Equiv.swap (Fin.last k) i
  have hi (j : Fin k) : σ j.castSucc ≠ i := by
    intro heq
    have hlast : σ (Fin.last k) = i := Equiv.swap_apply_left _ _
    exact Fin.castSucc_ne_last j (σ.injective (heq.trans hlast.symm))
  choose f hf using fun j : Fin k => Fin.exists_succAbove_eq (hi j)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Fin.castSucc_injective
    apply σ.injective
    exact (hf a).symm.trans ((congrArg i.succAbove hab).trans (hf b))
  let r := Equiv.ofBijective f ⟨hf_inj, Finite.surjective_of_injective hf_inj⟩
  exact ⟨r, fun j => (hf j).symm⟩

end StratificationTheory
