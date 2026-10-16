module

public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

public section

open HarmonicMaps

namespace StratificationTheory

private theorem signed_cap_tangent_abs {k : ℕ} (i : Fin (k + 1)) (side : Bool)
    (x : Domain k) (h : ℝ) (l : Fin (k + 1)) (hli : l ≠ i) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)
    ∃ a : Fin k, |cubicalSignedFaceIsometry k i side
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) h)) l| = |x a| := by
  intro e
  have hsne : (Equiv.swap (Fin.last k) i) l ≠ Fin.last k := by
    intro heq
    apply hli
    apply (Equiv.swap (Fin.last k) i).injective
    exact heq.trans (Equiv.swap_apply_right (Fin.last k) i).symm
  obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last hsne
  refine ⟨a, ?_⟩
  rw [cubicalSignedFaceIsometry_abs_apply, ← ha]
  have hBase : e.symm (x, EuclideanSpace.single (0 : Fin 1) h) a.castSucc = x a := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) h))).1 a = x a
    rw [e.apply_symm_apply]
  rw [hBase]

/-- A genuine nested signed face cap has exactly its two displayed active
physical coordinates. Every other coordinate remains strictly inside the
unit interval, in every dimension including an empty free-coordinate set. -/
theorem cubical_double_facet_active_coordinates {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1)) (sideI sideJ : Bool)
    (x : Domain k) (hx : ∀ a : Fin k, |x a| < 1) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 1) (m := 1)
    let inner := cubicalSignedFaceIsometry k j sideJ
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    let y := cubicalSignedFaceIsometry (k + 1) i sideI
      (E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1))
    let l := (Equiv.swap (Fin.last (k + 1)) i) j.castSucc
    l ≠ i ∧ y i = (if sideI then (1 : ℝ) else -1) ∧
      y l = (if sideJ then (1 : ℝ) else -1) ∧
      (∀ a, a ≠ i → a ≠ l → |y a| < 1) ∧
      (∀ a, |y a| = 1 ↔ a = i ∨ a = l) := by
  intro e E inner y l
  have hli : l ≠ i := by
    intro heq
    apply Fin.castSucc_ne_last j
    apply (Equiv.swap (Fin.last (k + 1)) i).injective
    exact heq.trans (Equiv.swap_apply_left (Fin.last (k + 1)) i).symm
  have hEt : E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1)
      (Fin.last (k + 1)) = 1 := by
    change (E (E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1))).2 0 = 1
    rw [E.apply_symm_apply]
    rfl
  have het : e.symm (x, EuclideanSpace.single (0 : Fin 1) 1) (Fin.last k) = 1 := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).2 0 = 1
    rw [e.apply_symm_apply]
    rfl
  have hyi : y i = (if sideI then (1 : ℝ) else -1) := by
    dsimp only [y]
    rw [cubicalSignedFaceIsometry_coordinate, if_pos rfl, hEt]
  have hyl : y l = (if sideJ then (1 : ℝ) else -1) := by
    dsimp only [y, l]
    rw [cubicalSignedFaceIsometry_apply, if_neg (Fin.castSucc_ne_last j)]
    have hBase : E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1) j.castSucc = inner j := by
      change (E (E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1))).1 j = inner j
      rw [E.apply_symm_apply]
    rw [hBase]
    dsimp only [inner]
    rw [cubicalSignedFaceIsometry_coordinate, if_pos rfl, het]
  have hStrict (a : Fin (k + 2)) (hai : a ≠ i) (hal : a ≠ l) : |y a| < 1 := by
    have hsa : (Equiv.swap (Fin.last (k + 1)) i) a ≠ Fin.last (k + 1) := by
      intro heq
      apply hai
      apply (Equiv.swap (Fin.last (k + 1)) i).injective
      exact heq.trans (Equiv.swap_apply_right (Fin.last (k + 1)) i).symm
    obtain ⟨b, hb⟩ := Fin.eq_castSucc_of_ne_last hsa
    have hbj : b ≠ j := by
      intro heq
      apply hal
      apply (Equiv.swap (Fin.last (k + 1)) i).injective
      dsimp only [l]
      rw [Equiv.swap_apply_self, ← hb, heq]
    obtain ⟨c, hc⟩ := signed_cap_tangent_abs j sideJ x 1 b hbj
    dsimp only [y]
    rw [cubicalSignedFaceIsometry_abs_apply, ← hb]
    have hBase : E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1) b.castSucc = inner b := by
      change (E (E.symm (inner, EuclideanSpace.single (0 : Fin 1) 1))).1 b = inner b
      rw [E.apply_symm_apply]
    rw [hBase, hc]
    exact hx c
  refine ⟨hli, hyi, hyl, hStrict, ?_⟩
  intro a
  constructor
  · intro ha
    by_cases hai : a = i
    · exact Or.inl hai
    · by_cases hal : a = l
      · exact Or.inr hal
      · exact False.elim ((ne_of_lt (hStrict a hai hal)) ha)
  · rintro (rfl | rfl)
    · rw [hyi]; cases sideI <;> norm_num
    · rw [hyl]; cases sideJ <;> norm_num

private theorem signed_active_pair_membership {D : ℕ} (y : Domain D)
    (i l : Fin D) (sideI sideL : Bool)
    (hyi : y i = (if sideI then (1 : ℝ) else -1))
    (hyl : y l = (if sideL then (1 : ℝ) else -1))
    (hActive : ∀ a, |y a| = 1 ↔ a = i ∨ a = l)
    (a : Fin D) (side : Bool) :
    (a, side) ∈ ({(i, sideI), (l, sideL)} : Finset (Fin D × Bool)) ↔
      |y a| = 1 ∧ y a = (if side then (1 : ℝ) else -1) := by
  have hSign {s t : Bool} (h : (if s then (1 : ℝ) else -1) = (if t then (1 : ℝ) else -1)) : s = t := by
    cases s
    · cases t
      · rfl
      · change (-1 : ℝ) = 1 at h
        norm_num at h
    · cases t
      · change (1 : ℝ) = -1 at h
        norm_num at h
      · rfl
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨(hActive a).mpr (Or.inl rfl), hyi⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨(hActive a).mpr (Or.inr rfl), hyl⟩
  · rintro ⟨ha, hv⟩
    rcases (hActive a).mp ha with rfl | rfl
    · exact Or.inl (Prod.ext rfl (hSign (hv.symm.trans hyi)))
    · exact Or.inr (Prod.ext rfl (hSign (hv.symm.trans hyl)))

/-- Two genuine nested signed caps representing the same physical point
have the same unordered signed normal pair. This identifies the physical
codimension-two face independently of the order of its two facet charts. -/
theorem cubical_double_facet_signed_normals_unique {k : ℕ}
    (i i' : Fin (k + 2)) (j j' : Fin (k + 1))
    (sideI sideJ sideI' sideJ' : Bool) (x x' : Domain k)
    (hx : ∀ a : Fin k, |x a| < 1) (hx' : ∀ a : Fin k, |x' a| < 1) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 1) (m := 1)
    let cap := fun (a : Fin (k + 2)) (b : Fin (k + 1)) (s t : Bool) (v : Domain k) =>
      cubicalSignedFaceIsometry (k + 1) a s
        (E.symm (cubicalSignedFaceIsometry k b t
          (e.symm (v, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1))
    cap i j sideI sideJ x = cap i' j' sideI' sideJ' x' →
      ({(i, sideI), ((Equiv.swap (Fin.last (k + 1)) i) j.castSucc, sideJ)} :
        Finset (Fin (k + 2) × Bool)) =
      {(i', sideI'), ((Equiv.swap (Fin.last (k + 1)) i') j'.castSucc, sideJ')} := by
  intro e E cap hSame
  obtain ⟨_, hyi, hyl, _, hActive⟩ :=
    cubical_double_facet_active_coordinates i j sideI sideJ x hx
  obtain ⟨_, hyi', hyl', _, hActive'⟩ :=
    cubical_double_facet_active_coordinates i' j' sideI' sideJ' x' hx'
  change cap i j sideI sideJ x i = _ at hyi
  change cap i j sideI sideJ x ((Equiv.swap (Fin.last (k + 1)) i) j.castSucc) = _ at hyl
  change ∀ a, |cap i j sideI sideJ x a| = 1 ↔ _ at hActive
  change cap i' j' sideI' sideJ' x' i' = _ at hyi'
  change cap i' j' sideI' sideJ' x' ((Equiv.swap (Fin.last (k + 1)) i') j'.castSucc) = _ at hyl'
  change ∀ a, |cap i' j' sideI' sideJ' x' a| = 1 ↔ _ at hActive'
  ext p
  obtain ⟨a, side⟩ := p
  rw [signed_active_pair_membership _ _ _ _ _ hyi hyl hActive,
    signed_active_pair_membership _ _ _ _ _ hyi' hyl' hActive']
  rw [hSame]

end StratificationTheory
