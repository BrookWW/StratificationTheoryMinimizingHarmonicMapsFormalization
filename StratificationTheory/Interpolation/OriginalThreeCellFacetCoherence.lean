module

public import StratificationTheory.Interpolation.OriginalPrismCommonEdgeCoherence
public import StratificationTheory.Foundation.CubicalThreeFacetIncidence

public section

open HarmonicMaps

namespace StratificationTheory

private theorem facet_coherence_of_representatives {n q : ℕ}
    (w : Fin 2 → Domain (n + 3) → Ambient q)
    (Dw : Fin 2 → Domain (n + 3) → Gradient (n + 3) q)
    (rep : Fin 2 → Fin (n + 3) → Domain (n + 3) → Ambient q)
    (coord : Fin 3 ↪ Fin (n + 3)) (ε : ℝ) (y : Domain (n + 3))
    (i j : Fin 3) (sideI sideJ : Bool) (hij : i ≠ j) :
    let pair : Fin 3 → (Fin 2 ↪ Fin (n + 3)) := fun k =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) k).toEmbedding).trans coord
    let δ := fun side : Bool => if side then ε else 0
    let origin := fun k side => y + δ side • EuclideanSpace.single (coord k) (1 : ℝ)
    let other := fun k : Fin 2 => (Equiv.swap (0 : Fin 2) 1) k
    let embed := fun (c : Fin 2 ↪ Fin (n + 3)) (Y : Domain (n + 3)) (t : Domain 2) =>
      Y + t 0 • EuclideanSpace.single (c 0) (1 : ℝ) + t 1 • EuclideanSpace.single (c 1) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let edge := fun (k : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 k true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (δ side)))
    let F := fun c Y k side l s => rep l (c (other k)) (embed c Y (edge k side s))
    let f := fun c Y k side l s => w l (embed c Y (edge k side s))
    let g := fun c Y k side l s => Dw l (embed c Y (edge k side s)) (c (other k))
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => A + (ε / 2) • z
    let V := fun c Y k side (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F c Y k side (0 : Fin 2) ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F c Y k side (1 : Fin 2) ((b (T z)).1 0)
    ∃ a b : Fin 2,
      pair i a = coord j ∧ pair j b = coord i ∧
      pair i (other a) = pair j (other b) ∧
      (∀ l s, F (pair i) (origin i sideI) a sideJ l s = F (pair j) (origin j sideJ) b sideI l s) ∧
      (∀ l s, f (pair i) (origin i sideI) a sideJ l s = f (pair j) (origin j sideJ) b sideI l s) ∧
      (∀ l s, g (pair i) (origin i sideI) a sideJ l s = g (pair j) (origin j sideJ) b sideI l s) ∧
      V (pair i) (origin i sideI) a sideJ = V (pair j) (origin j sideJ) b sideI := by
  intro pair δ origin other embed b edge F f g A T V
  obtain ⟨a, b₀, ha, hb, hT, hOrigin⟩ :=
    cubical_three_facet_shared_edge_origins coord ε y i j sideI sideJ hij
  refine ⟨a, b₀, ha, hb, hT, ?_⟩
  have hAxis (c : Fin 2 ↪ Fin (n + 3)) (Y : Domain (n + 3)) (k : Fin 2) (s t : ℝ) :
      embed c Y (cubicalSignedFaceIsometry 1 k true
        (b.symm (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) t))) =
        (Y + t • EuclideanSpace.single (c k) (1 : ℝ)) + s • EuclideanSpace.single (c (other k)) (1 : ℝ) := by
    have h := two_vector_square_axis Y (EuclideanSpace.single (c 0) (1 : ℝ))
      (EuclideanSpace.single (c 1) (1 : ℝ)) k (EuclideanSpace.single (0 : Fin 1) s) t
    fin_cases k <;> simpa [embed, b, other] using h
  have hPoint (s : ℝ) : embed (pair i) (origin i sideI) (edge a sideJ s) =
      embed (pair j) (origin j sideJ) (edge b₀ sideI s) := by
    change embed (pair i) (origin i sideI) (cubicalSignedFaceIsometry 1 a true (b.symm
      (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) (δ sideJ)))) =
        embed (pair j) (origin j sideJ) (cubicalSignedFaceIsometry 1 b₀ true (b.symm
          (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) (δ sideI))))
    rw [hAxis, hAxis, hOrigin, hT]
  have hF (l : Fin 2) (s : ℝ) :
      F (pair i) (origin i sideI) a sideJ l s = F (pair j) (origin j sideJ) b₀ sideI l s := by
    change rep l (pair i (other a)) (embed (pair i) (origin i sideI) (edge a sideJ s)) = _
    rw [hT, hPoint]
  refine ⟨hF, fun l s => congrArg (w l) (hPoint s), ?_, ?_⟩
  · intro l s
    change Dw l (embed (pair i) (origin i sideI) (edge a sideJ s)) (pair i (other a)) = _
    rw [hT, hPoint]
  · funext z
    change (1 - (b (T z)).2 0 / ε) • F (pair i) (origin i sideI) a sideJ 0 ((b (T z)).1 0) +
      ((b (T z)).2 0 / ε) • F (pair i) (origin i sideI) a sideJ 1 ((b (T z)).1 0) = _
    rw [hF, hF]

/-- The actual first-prism constructions on two distinct spatial facets
of one original coordinate three-cell prescribe exactly the same affine
connector on their shared physical edge, with the same original raw edge
values and columns. -/
theorem original_three_cell_facet_edge_coherence {n q : ℕ}
    (w : Fin 2 → Domain (n + 3) → Ambient q)
    (Dw : Fin 2 → Domain (n + 3) → Gradient (n + 3) q)
    (coord : Fin 3 ↪ Fin (n + 3)) (ε : ℝ) (y : Domain (n + 3))
    (i j : Fin 3) (sideI sideJ : Bool) (hij : i ≠ j) :
    let pair : Fin 3 → (Fin 2 ↪ Fin (n + 3)) := fun k =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) k).toEmbedding).trans coord
    let δ := fun side : Bool => if side then ε else 0
    let origin := fun k side => y + δ side • EuclideanSpace.single (coord k) (1 : ℝ)
    let rep := fun (l : Fin 2) (k : Fin (n + 3)) =>
      coordinatePermACLRepresentative (Equiv.swap (Fin.last (n + 2)) k) (-1) 1 (w l) (Dw l)
    let other := fun k : Fin 2 => (Equiv.swap (0 : Fin 2) 1) k
    let embed := fun (c : Fin 2 ↪ Fin (n + 3)) (Y : Domain (n + 3)) (t : Domain 2) =>
      Y + t 0 • EuclideanSpace.single (c 0) (1 : ℝ) + t 1 • EuclideanSpace.single (c 1) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let edge := fun (k : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 k true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (δ side)))
    let F := fun c Y k side l s => rep l (c (other k)) (embed c Y (edge k side s))
    let f := fun c Y k side l s => w l (embed c Y (edge k side s))
    let g := fun c Y k side l s => Dw l (embed c Y (edge k side s)) (c (other k))
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => A + (ε / 2) • z
    let V := fun c Y k side (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F c Y k side (0 : Fin 2) ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F c Y k side (1 : Fin 2) ((b (T z)).1 0)
    ∃ a b : Fin 2,
      pair i a = coord j ∧ pair j b = coord i ∧
      pair i (other a) = pair j (other b) ∧
      (∀ l s, F (pair i) (origin i sideI) a sideJ l s = F (pair j) (origin j sideJ) b sideI l s) ∧
      (∀ l s, f (pair i) (origin i sideI) a sideJ l s = f (pair j) (origin j sideJ) b sideI l s) ∧
      (∀ l s, g (pair i) (origin i sideI) a sideJ l s = g (pair j) (origin j sideJ) b sideI l s) ∧
      V (pair i) (origin i sideI) a sideJ = V (pair j) (origin j sideJ) b sideI := by
  intro pair δ origin rep other embed b edge F f g A T V
  dsimp only [F, V]
  generalize hRep : rep = R
  exact facet_coherence_of_representatives w Dw R coord ε y i j sideI sideJ hij

end StratificationTheory
