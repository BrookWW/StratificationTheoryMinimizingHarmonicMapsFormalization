module

public import StratificationTheory.Foundation.PrismLowerCellLookup

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- Actual canonical sorted child indices commute under two spatial
normal deletions, with the exact same original physical lower cell. -/
theorem canonical_sorted_child_physical_indices_commute {N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    ∀ (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (_hAxes : ∀ r p i s, (child r p i s).val.val.1 = i.succAboveEmb.trans p.val.val.1)
      (_hOrigin : ∀ r p i s, (child r p i s).val.val.2 =
        p.val.val.2 + (if s then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ))
      {k : ℕ} (p : Cell (k + 2)) (i : Fin (k + 2)) (a : Fin (k + 1)) (sideI sideJ : Bool),
    let j := i.succAbove a
    let b := a.predAbove i
    child k (child (k + 1) p i sideI) a sideJ =
      child k (child (k + 1) p j sideJ) b sideI := by
  intro Cell child hAxes hOrigin k p i a sideI sideJ j b
  apply Subtype.ext
  apply original_physical_cell_index_eq grid offset ε
  · rw [hAxes, hAxes, hAxes, hAxes]
    apply Function.Embedding.ext
    intro s
    change p.val.val.1 (i.succAbove (a.succAbove s)) =
      p.val.val.1 ((i.succAbove a).succAbove ((a.predAbove i).succAbove s))
    exact congrArg p.val.val.1 (Fin.succAbove_succAbove_succAbove_predAbove i a s).symm
  · rw [hOrigin, hOrigin, hOrigin, hOrigin, hAxes, hAxes]
    change (p.val.val.2 + (if sideI then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ)) +
        (if sideJ then ε else 0) • EuclideanSpace.single (p.val.val.1 (i.succAbove a)) (1 : ℝ) =
      (p.val.val.2 + (if sideJ then ε else 0) • EuclideanSpace.single (p.val.val.1 j) (1 : ℝ)) +
        (if sideI then ε else 0) • EuclideanSpace.single (p.val.val.1 (j.succAbove b)) (1 : ℝ)
    have hNormal : j.succAbove b = i := Fin.succAbove_succAbove_predAbove i a
    rw [hNormal]
    change (p.val.val.2 + _) + _ = (p.val.val.2 + _) + _
    abel


/-- Canonical sorted source-cap and filled lower-cell keys have one lookup
on unordered signed normal pairs. Actual child metadata prove all required
exchange compatibility internally. -/
theorem exists_sorted_prism_lower_cell_lookup {N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    ∀ (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (_hAxes : ∀ r p i s, (child r p i s).val.val.1 = i.succAboveEmb.trans p.val.val.1)
      (_hOrigin : ∀ r p i s, (child r p i s).val.val.2 =
        p.val.val.2 + (if s then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ))
      {k : ℕ} (p : Cell (k + 2)),
    ∃ lookup : Finset (Fin (k + 3) × Bool) → (Cell (k + 1) × Bool) ⊕ Cell k,
      (∀ (i : Fin (k + 2)) (s t : Bool),
        lookup {(i.castSucc, s), (Fin.last (k + 2), t)} = Sum.inl (child (k + 1) p i s, t)) ∧
      ∀ (i : Fin (k + 2)) (a : Fin (k + 1)) (s t : Bool),
        lookup {(i.castSucc, s), ((i.succAbove a).castSucc, t)} =
          Sum.inr (child k (child (k + 1) p i s) a t) := by
  intro Cell child hAxes hOrigin k p
  classical
  let C := (Fin (k + 2) × Bool × Bool) ⊕ (Fin (k + 2) × Fin (k + 1) × Bool × Bool)
  let L := (Cell (k + 1) × Bool) ⊕
    Cell k
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
        exact congrArg Sum.inr (canonical_sorted_child_physical_indices_commute grid offset ε child hAxes hOrigin p i a s t)
  obtain ⟨lookup, hLookup⟩ := exists_ambient_representative_of_compatible_charts
    (fun _ : C => (Set.univ : Set Unit)) (fun c (_ : Unit) => normals c) (fun c (_ : Unit) => value c)
      (fun c c' _ _ _ _ h => hCompat c c' h)
  refine ⟨lookup, ?_, ?_⟩
  · intro i s t
    exact hLookup (Sum.inl (i, s, t)) () (mem_univ _)
  · intro i a s t
    exact hLookup (Sum.inr (i, a, s, t)) () (mem_univ _)

end StratificationTheory
