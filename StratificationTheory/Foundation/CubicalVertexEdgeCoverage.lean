module

public import StratificationTheory.Foundation.ScaledGridCubeEdges

/-! # Genuine vertex edges and their complete cubical chart indices -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The cubical edge chart is the literal affine edge of its Boolean
vertex, for every real parameter, when its tangent vertex coordinate is zero. -/
theorem cubical_edge_chart_of_vertex {d : ℕ} (ε : ℝ) (normal : Fin (d + 1))
    (v : Fin (d + 1) → Bool) (hv : v normal = false) (s : ℝ) :
    let σ := Equiv.swap (Fin.last d) normal
    let base : Domain d := WithLp.toLp 2 (fun j : Fin d => if v (σ j.castSucc) then ε else 0)
    let vertex : Domain (d + 1) := WithLp.toLp 2 (fun j => if v j then (1 : ℝ) else 0)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    cubicalSignedFaceIsometry d normal true (e.symm (base, EuclideanSpace.single (0 : Fin 1) s)) =
      ε • vertex + s • EuclideanSpace.single normal (1 : ℝ) := by
  intro σ base vertex e
  ext k
  obtain ⟨j, rfl⟩ := σ.surjective k
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [cubicalSignedFaceIsometry_apply]
    simp only [ite_true]
    have hLast : e.symm (base, EuclideanSpace.single (0 : Fin 1) s) (Fin.last d) = s := by
      change (e (e.symm (base, EuclideanSpace.single (0 : Fin 1) s))).2 0 = s
      rw [e.apply_symm_apply]
      rfl
    rw [hLast]
    simp [σ, vertex, hv]
  · rw [cubicalSignedFaceIsometry_apply]
    simp only [Fin.castSucc_ne_last, ite_false]
    have hBase : e.symm (base, EuclideanSpace.single (0 : Fin 1) s) j.castSucc = base j := by
      change (e (e.symm (base, EuclideanSpace.single (0 : Fin 1) s))).1 j = base j
      rw [e.apply_symm_apply]
    rw [hBase]
    have hne : σ j.castSucc ≠ normal := by
      intro h
      exact (Fin.castSucc_ne_last j) (σ.injective (h.trans (Equiv.swap_apply_left _ _).symm))
    cases hside : v (σ j.castSucc) <;>
      simp [base, vertex, hside, hne]

/-- Recording the tangent direction and all transverse Boolean vertex bits
loses no genuine cubical edge. -/
theorem cubical_vertex_edge_chart_index_injective (d : ℕ) :
    Function.Injective (fun x : {e : Fin (d + 1) × (Fin (d + 1) → Bool) // e.2 e.1 = false} =>
      (x.val.1, fun j : Fin d => x.val.2 ((Equiv.swap (Fin.last d) x.val.1) j.castSucc))) := by
  intro x y h
  rcases x with ⟨⟨nx, vx⟩, hx⟩
  rcases y with ⟨⟨ny, vy⟩, hy⟩
  have hn : nx = ny := congrArg Prod.fst h
  subst ny
  let σ := Equiv.swap (Fin.last d) nx
  have hBits : (fun j : Fin d => vx (σ j.castSucc)) = (fun j : Fin d => vy (σ j.castSucc)) :=
    congrArg Prod.snd h
  apply Subtype.ext
  change (nx, vx) = (nx, vy)
  apply congrArg (fun f : Fin (d + 1) → Bool => (nx, f))
  funext k
  obtain ⟨j, rfl⟩ := σ.surjective k
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [σ, Equiv.swap_apply_left] using hx.trans hy.symm
  · exact congrFun hBits j

/-- The actual chart identity of one fixed lattice edge family covers every
Boolean parent-cell edge. The same family is used throughout the conclusion. -/
theorem scaled_grid_edge_family_covers_vertices {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let I := Fin (n + 2) × (Fin (n + 1) → Bool)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let vertex := fun i : I =>
      (WithLp.toLp 2 (fun j : Fin (n + 1) => if i.2 j then ε else 0) : Domain (n + 1))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    ∀ shift : I → L,
    (∀ (i : I) (z : L) (s : ℝ), y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
      y z + cubicalSignedFaceIsometry (n + 1) i.1 true
        (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s))) →
    ∀ (z : L) (normal : Fin (n + 2)) (v : Fin (n + 2) → Bool), v normal = false →
      ∃ i : I, i.1 = normal ∧ ∀ s : ℝ,
        y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
          y z + ε • WithLp.toLp 2 (fun j => if v j then (1 : ℝ) else 0) +
            s • EuclideanSpace.single normal (1 : ℝ) := by
  intro grid L I y vertex e shift hChart z normal v hv
  let i : I := (normal, fun j => v ((Equiv.swap (Fin.last (n + 1)) normal) j.castSucc))
  refine ⟨i, rfl, ?_⟩
  intro s
  rw [hChart i z s]
  change y z + cubicalSignedFaceIsometry (n + 1) normal true
    (e.symm (WithLp.toLp 2 (fun j : Fin (n + 1) => if v ((Equiv.swap (Fin.last (n + 1)) normal) j.castSucc) then ε else 0),
      EuclideanSpace.single (0 : Fin 1) s)) = _
  rw [cubical_edge_chart_of_vertex ε normal v hv s]
  exact (add_assoc _ _ _).symm

/-- Every genuine parent-vertex origin with zero tangent displacement is
covered by the same actual lattice edge family, with no second shift choice. -/
theorem scaled_grid_edge_family_covers_discrete_origin {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let I := Fin (n + 2) × (Fin (n + 1) → Bool)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let vertex := fun i : I =>
      (WithLp.toLp 2 (fun j : Fin (n + 1) => if i.2 j then ε else 0) : Domain (n + 1))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    ∀ shift : I → L,
    (∀ (i : I) (z : L) (s : ℝ), y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
      y z + cubicalSignedFaceIsometry (n + 1) i.1 true
        (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s))) →
    ∀ (z : L) (normal : Fin (n + 2)) (x : Domain (n + 2)),
    x normal = (y z) normal →
    (∀ j, x j - (y z) j = 0 ∨ x j - (y z) j = ε) →
    ∃ i : I, i.1 = normal ∧ ∀ s : ℝ,
      y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
        x + s • EuclideanSpace.single normal (1 : ℝ) := by
  intro grid L I y vertex e shift hChart z normal x hNormal hDiscrete
  classical
  let v := fun j => if x j - (y z) j = ε then true else false
  have hv : v normal = false := by
    have hne : x normal - (y z) normal ≠ ε := by rw [hNormal, sub_self]; exact hε.ne
    simp only [v, if_neg hne]
  have hVertex : x = y z + ε • WithLp.toLp 2 (fun j => if v j then (1 : ℝ) else 0) := by
    ext j
    change x j = (y z) j + ε * (if v j then (1 : ℝ) else 0)
    rcases hDiscrete j with hj | hj
    · have hne : x j - (y z) j ≠ ε := by rw [hj]; exact hε.ne
      simp only [v, if_neg hne, Bool.false_eq_true, ite_false, mul_zero, add_zero]
      linarith only [hj]
    · simp only [v, if_pos hj, ite_true, mul_one]
      linarith only [hj]
  obtain ⟨i, hi, hEdge⟩ := scaled_grid_edge_family_covers_vertices hε offset shift hChart z normal v hv
  refine ⟨i, hi, ?_⟩
  intro s
  rw [hEdge, ← hVertex]

/-- The full edge index cardinal is a dimension-only quantity. -/
theorem cubical_full_edge_index_card (n : ℕ) :
    Fintype.card (Fin (n + 2) × (Fin (n + 1) → Bool)) = (n + 2) * 2 ^ (n + 1) := by simp

end StratificationTheory
