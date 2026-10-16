module

public import StratificationTheory.Foundation.CanonicalChildIndexCommutation
public import StratificationTheory.Foundation.UnorderedSignedPairLookup
public import StratificationTheory.Foundation.CompatibleChartValueExtension

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- The actual source-cap or filled lower-cell key of every codimension-two
prism face is determined by its unordered signed physical normals. Canonical
child metadata produce this lookup internally, including exchange of two
spatial normals and both orders of a spatial normal with time. -/
theorem exists_prism_lower_cell_lookup {N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (child : (r : ℕ) → originalPhysicalCellCarrier (r + 1) grid offset ε →
      Fin (r + 1) → Bool → originalPhysicalCellCarrier r grid offset ε)
    (hAxes : ∀ r p i s, (child r p i s).val.1 = i.succAboveEmb.trans p.val.1)
    (hOrigin : ∀ r p i s, (child r p i s).val.2 =
      p.val.2 + (if s then ε else 0) • EuclideanSpace.single (p.val.1 i) (1 : ℝ))
    {k : ℕ} (p : originalPhysicalCellCarrier (k + 2) grid offset ε) :
    ∃ lookup : Finset (Fin (k + 3) × Bool) →
        (originalPhysicalCellCarrier (k + 1) grid offset ε × Bool) ⊕
          originalPhysicalCellCarrier k grid offset ε,
      (∀ (i : Fin (k + 2)) (s t : Bool),
        lookup {(i.castSucc, s), (Fin.last (k + 2), t)} =
          Sum.inl (child (k + 1) p i s, t)) ∧
      ∀ (i : Fin (k + 2)) (a : Fin (k + 1)) (s t : Bool),
        lookup {(i.castSucc, s), ((i.succAbove a).castSucc, t)} =
          Sum.inr (child k (child (k + 1) p i s) a t) := by
  classical
  let C := (Fin (k + 2) × Bool × Bool) ⊕ (Fin (k + 2) × Fin (k + 1) × Bool × Bool)
  let L := (originalPhysicalCellCarrier (k + 1) grid offset ε × Bool) ⊕
    originalPhysicalCellCarrier k grid offset ε
  let normals : C → Finset (Fin (k + 3) × Bool) := Sum.elim
    (fun c => {(c.1.castSucc, c.2.1), (Fin.last (k + 2), c.2.2)})
    (fun c => {(c.1.castSucc, c.2.2.1), ((c.1.succAbove c.2.1).castSucc, c.2.2.2)})
  let value : C → L := Sum.elim
    (fun c => Sum.inl (child (k + 1) p c.1 c.2.1, c.2.2))
    (fun c => Sum.inr (child k (child (k + 1) p c.1 c.2.2.1) c.2.1 c.2.2.2))
  have hTimeNotSpatial (i j l : Fin (k + 2)) (s t u v : Bool) :
      ({(i.castSucc, s), (Fin.last (k + 2), t)} : Finset (Fin (k + 3) × Bool)) ≠
        {(j.castSucc, u), (l.castSucc, v)} := by
    intro h
    have hmem : (Fin.last (k + 2), t) ∈
        ({(j.castSucc, u), (l.castSucc, v)} : Finset (Fin (k + 3) × Bool)) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · exact Fin.castSucc_ne_last j (congrArg Prod.fst hmem).symm
    · exact Fin.castSucc_ne_last l (congrArg Prod.fst hmem).symm
  have hCompat (c c' : C) (h : normals c = normals c') : value c = value c' := by
    rcases c with ⟨i, s, t⟩ | ⟨i, a, s, t⟩ <;>
      rcases c' with ⟨j, u, v⟩ | ⟨j, b, u, v⟩
    · change ({(i.castSucc, s), (Fin.last (k + 2), t)} : Finset (Fin (k + 3) × Bool)) =
        {(j.castSucc, u), (Fin.last (k + 2), v)} at h
      rcases (signed_normal_pair_eq_iff _ _ _ _ _ _ _ _ (Fin.castSucc_ne_last i)).mp h with
        ⟨hi, ht⟩ | ⟨hi, _⟩
      · have hij : i = j := Fin.castSucc_injective _ (congrArg Prod.fst hi)
        have hsu : s = u := congrArg Prod.snd hi
        have htv : t = v := congrArg Prod.snd ht
        subst j; subst u; subst v; rfl
      · exact False.elim (Fin.castSucc_ne_last i (congrArg Prod.fst hi))
    · exact False.elim (hTimeNotSpatial i j (j.succAbove b) s t u v h)
    · exact False.elim (hTimeNotSpatial j i (i.succAbove a) u v s t h.symm)
    · change ({(i.castSucc, s), ((i.succAbove a).castSucc, t)} : Finset (Fin (k + 3) × Bool)) =
        {(j.castSucc, u), ((j.succAbove b).castSucc, v)} at h
      have hne : i.castSucc ≠ (i.succAbove a).castSucc := by
        intro hEq
        exact Fin.succAbove_ne i a (Fin.castSucc_injective _ hEq).symm
      rcases (signed_normal_pair_eq_iff _ _ _ _ _ _ _ _ hne).mp h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · have hij : i = j := Fin.castSucc_injective _ (congrArg Prod.fst hi)
        have hsu : s = u := congrArg Prod.snd hi
        have htv : t = v := congrArg Prod.snd hj
        subst j; subst u; subst v
        have hab : a = b := Fin.succAbove_right_injective
          (Fin.castSucc_injective _ (congrArg Prod.fst hj))
        subst b
        rfl
      · have hij : i = j.succAbove b := Fin.castSucc_injective _ (congrArg Prod.fst hi)
        have hji : i.succAbove a = j := Fin.castSucc_injective _ (congrArg Prod.fst hj)
        have hsv : s = v := congrArg Prod.snd hi
        have htu : t = u := congrArg Prod.snd hj
        subst j; subst v; subst u
        have hb : b = a.predAbove i := Fin.succAbove_right_injective
          (hij.symm.trans (Fin.succAbove_succAbove_predAbove i a).symm)
        subst b
        change Sum.inr _ = Sum.inr _
        exact congrArg Sum.inr (canonical_child_physical_indices_commute grid offset ε child hAxes hOrigin p i a s t)
  obtain ⟨lookup, hLookup⟩ := exists_ambient_representative_of_compatible_charts
    (fun _ : C => (Set.univ : Set Unit)) (fun c (_ : Unit) => normals c) (fun c (_ : Unit) => value c)
      (fun c c' _ _ _ _ h => hCompat c c' h)
  refine ⟨lookup, ?_, ?_⟩
  · intro i s t
    exact hLookup (Sum.inl (i, s, t)) () (mem_univ _)
  · intro i a s t
    exact hLookup (Sum.inr (i, a, s, t)) () (mem_univ _)

end StratificationTheory
