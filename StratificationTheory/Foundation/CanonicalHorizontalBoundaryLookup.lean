module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps

namespace StratificationTheory

/-- Actual original horizontal face identities retain the same global
source-cap lookup when the two physical normals are listed in either order.
The assertion applies equally to raw values and actual physical charts. -/
theorem canonical_horizontal_boundary_lookup {k : ℕ} {C F Y : Type*}
    (child : Fin (k + 2) → Bool → C)
    (parentFace : Bool → Domain (k + 2) → Y)
    (sourceFace : C → Bool → Domain (k + 1) → Y)
    (filledFace : F → Domain (k + 1) → Y)
    (R : Fin (k + 2) → Domain (k + 1) → Domain (k + 1))
    (lookup : Finset (Fin (k + 3) × Bool) → (C × Bool) ⊕ F)
    (hLookup : ∀ j s t, lookup {(j.castSucc, s), (Fin.last (k + 2), t)} = Sum.inl (child j s, t)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 1) (m := 1)
    let cap := fun (j : Fin (k + 2)) (s : Bool) (x : Domain (k + 1)) =>
      cubicalSignedFaceIsometry (k + 1) j s (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    let global := Sum.elim (fun c => sourceFace c.1 c.2) filledFace
    (∀ t j s x, parentFace t (cap j s x) = sourceFace (child j s) t (R j x)) →
    ∀ t j s x, parentFace t (cap j s x) =
      global (lookup {(Fin.last (k + 2), t), (j.castSucc, s)}) (R j x) := by
  intro e cap global hFace t j s x
  rw [Finset.pair_comm, hLookup]
  exact hFace t j s x

end StratificationTheory
