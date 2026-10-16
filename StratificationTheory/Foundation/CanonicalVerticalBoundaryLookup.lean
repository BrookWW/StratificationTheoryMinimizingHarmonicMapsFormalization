module

public import StratificationTheory.Foundation.CubicalSignedFrameBlock
public import Mathlib.Data.Fin.Tuple.Basic

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- The canonical vertical-face frame sends each raw old boundary class
to the actual global source-cap or filled lower-cell key determined by
the signed parent normals. -/
theorem canonical_vertical_boundary_lookup_value {k : ℕ} {Cell : ℕ → Type*} {Y : Type*}
    (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
    (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Equiv.Perm (Fin (r + 1)))
    (parent : Cell (k + 2)) (i : Fin (k + 2)) (side : Bool)
    (p : Equiv.Perm (Fin (k + 2)))
    (hpTime : p i = Fin.last (k + 1))
    (hpSpatial : ∀ a : Fin (k + 1), p (i.succAbove a) = a.castSucc)
    (R : Fin (k + 2) → Domain (k + 1) → Domain (k + 1))
    (U : Cell (k + 1) → Bool → Domain (k + 1) → Y)
    (V : Cell k → Domain (k + 1) → Y)
    (lookup : Finset (Fin (k + 3) × Bool) → (Cell (k + 1) × Bool) ⊕ Cell k)
    (hTime : ∀ t : Bool, lookup {(i.castSucc, side), (Fin.last (k + 2), t)} =
      Sum.inl (child (k + 1) parent i side, t))
    (hSpatial : ∀ (a : Fin (k + 1)) (t : Bool),
      lookup {(i.castSucc, side), ((i.succAbove a).castSucc, t)} =
        Sum.inr (child k (child (k + 1) parent i side) a t)) :
    let c := child (k + 1) parent i side
    let A := fun (a : Fin (k + 1)) =>
      cubicalSignedPermutation (k + 1) (frame k c a) (fun _ => true)
    let g : Fin (k + 2) → Bool → Domain (k + 1) → Y := fun j t => Fin.lastCases
      (motive := fun _ : Fin (k + 2) => Domain (k + 1) → Y)
      (U c t) (fun a => V (child k c a t) ∘ A a) j
    let global := Sum.elim (fun c => U c.1 c.2) V
    let normals := fun (j : Fin (k + 2)) (t : Bool) =>
      ({(i.castSucc, side), ((Equiv.swap (Fin.last (k + 2)) i.castSucc) j.castSucc, t)} :
        Finset (Fin (k + 3) × Bool))
    let arg : Fin (k + 2) → Bool → Domain (k + 1) → Domain (k + 1) := fun j _t x =>
      Fin.insertNth (α := fun _ : Fin (k + 2) => Domain (k + 1)) i (R j x) (fun a => A a (R j x)) j
    ∀ (j : Fin (k + 2)) (t : Bool) (x : Domain (k + 1)),
      g (p j) t (R j x) = global (lookup (normals j t)) (arg j t x) := by
  classical
  intro c A g global normals arg j t x
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · simp only [g, hpTime, Fin.lastCases_last, normals, Equiv.swap_apply_right,
      hTime, global, Sum.elim_inl, c, arg, Fin.insertNth_apply_same]
  · have hSwap : (Equiv.swap (Fin.last (k + 2)) i.castSucc) (i.succAbove a).castSucc =
        (i.succAbove a).castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · exact Fin.castSucc_ne_last _
      · exact fun h => Fin.succAbove_ne i a (Fin.castSucc_injective _ h)
    simp only [g, hpSpatial, Fin.lastCases_castSucc, normals, hSwap, hSpatial,
      global, Sum.elim_inr, arg, Fin.insertNth_apply_succAbove, Function.comp_apply, c]

/-- Actual outer-facet, old-cap, and finite-frame physical identities
compose into the same canonical unordered lower-cell chart. -/
theorem canonical_vertical_boundary_lookup_chart {k : ℕ} {Cell : ℕ → Type*} {Y : Type*}
    (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
    (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Equiv.Perm (Fin (r + 1)))
    (parent : Cell (k + 2)) (i : Fin (k + 2)) (side : Bool)
    (p : Equiv.Perm (Fin (k + 2)))
    (hpTime : p i = Fin.last (k + 1))
    (hpSpatial : ∀ a : Fin (k + 1), p (i.succAbove a) = a.castSucc)
    (R : Fin (k + 2) → Domain (k + 1) → Domain (k + 1))
    (U : Cell (k + 1) → Bool → Domain (k + 1) → Y)
    (V : Cell k → Domain (k + 1) → Y)
    (lookup : Finset (Fin (k + 3) × Bool) → (Cell (k + 1) × Bool) ⊕ Cell k)
    (hTime : ∀ t : Bool, lookup {(i.castSucc, side), (Fin.last (k + 2), t)} =
      Sum.inl (child (k + 1) parent i side, t))
    (hSpatial : ∀ (a : Fin (k + 1)) (t : Bool),
      lookup {(i.castSucc, side), ((i.succAbove a).castSucc, t)} =
        Sum.inr (child k (child (k + 1) parent i side) a t))
    (P : Cell (k + 1) → Domain (k + 2) → Y)
    (parentP : Domain (k + 3) → Y) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 1) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 2) (m := 1)
    let c := child (k + 1) parent i side
    let A := fun (a : Fin (k + 1)) =>
      cubicalSignedPermutation (k + 1) (frame k c a) (fun _ => true)
    let global := Sum.elim (fun c => U c.1 c.2) V
    let normals := fun (j : Fin (k + 2)) (t : Bool) =>
      ({(i.castSucc, side), ((Equiv.swap (Fin.last (k + 2)) i.castSucc) j.castSucc, t)} :
        Finset (Fin (k + 3) × Bool))
    let arg : Fin (k + 2) → Bool → Domain (k + 1) → Domain (k + 1) := fun j _t x =>
      Fin.insertNth (α := fun _ : Fin (k + 2) => Domain (k + 1)) i (R j x) (fun a => A a (R j x)) j
    (∀ z : Domain (k + 2), parentP (cubicalSignedFaceIsometry (k + 2) i.castSucc side
      (E.symm (z, EuclideanSpace.single (0 : Fin 1) 1))) =
        P c ((cubicalSignedPermutation (k + 2) p (fun _ => true)) z)) →
    (∀ (t : Bool) (x : Domain (k + 1)), P c
      (cubicalSignedFaceIsometry (k + 1) (Fin.last (k + 1)) t
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = U c t x) →
    (∀ (a : Fin (k + 1)) (t : Bool) (x : Domain (k + 1)), P c
      (cubicalSignedFaceIsometry (k + 1) a.castSucc t
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) =
          V (child k c a t) (A a x)) →
    (∀ (j : Fin (k + 2)) (x : Domain (k + 1)) (η : ℝ),
      (cubicalSignedPermutation (k + 2) p (fun _ => true))
        (cubicalSignedFaceIsometry (k + 1) j true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))) =
      cubicalSignedFaceIsometry (k + 1) (p j) true
        (e.symm (R j x, EuclideanSpace.single (0 : Fin 1) η))) →
    ∀ (j : Fin (k + 2)) (t : Bool) (x : Domain (k + 1)),
      parentP (cubicalSignedFaceIsometry (k + 2) i.castSucc side
        (E.symm (cubicalSignedFaceIsometry (k + 1) j t
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1))) =
      global (lookup (normals j t)) (arg j t x) := by
  intro e E c A global normals arg hOuter hTimeCap hSpatialCap hBlock j t x
  let g : Fin (k + 2) → Bool → Domain (k + 1) → Y := fun j t => Fin.lastCases
      (motive := fun _ : Fin (k + 2) => Domain (k + 1) → Y)
      (U c t) (fun a => V (child k c a t) ∘ A a) j

  have hOld (a : Fin (k + 2)) (t : Bool) (x : Domain (k + 1)) : P c
      (cubicalSignedFaceIsometry (k + 1) a t
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = g a t x := by
    refine Fin.lastCases ?_ (fun a => ?_) a
    · simpa only [g, Fin.lastCases_last] using hTimeCap t x
    · simpa only [g, Fin.lastCases_castSucc, Function.comp_apply] using hSpatialCap a t x
  have hCap : (cubicalSignedPermutation (k + 2) p (fun _ => true))
      (cubicalSignedFaceIsometry (k + 1) j t
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) =
      cubicalSignedFaceIsometry (k + 1) (p j) t
        (e.symm (R j x, EuclideanSpace.single (0 : Fin 1) 1)) := by
    rw [cubical_signed_face_native_height, hBlock,
      ← cubical_signed_face_native_height]
  exact (hOuter _).trans ((congrArg (P c) hCap).trans ((hOld (p j) t (R j x)).trans
    (canonical_vertical_boundary_lookup_value child frame parent i side p hpTime hpSpatial
      R U V lookup hTime hSpatial j t x)))

end StratificationTheory
