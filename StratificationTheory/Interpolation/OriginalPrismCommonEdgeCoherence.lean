module

public import StratificationTheory.Foundation.CoordinateGridCompatibility
public import StratificationTheory.Foundation.TwoVectorSquareTraceTransport

public section

open HarmonicMaps

namespace StratificationTheory

private theorem common_edge_data_of_representatives {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (rep : Fin 2 → Fin (n + 2) → Domain (n + 2) → Ambient q)
    (c₀ c₁ : Fin 2 ↪ Fin (n + 2)) (ε : ℝ) (y₀ y₁ : Domain (n + 2))
    (i₀ i₁ : Fin 2) (side₀ side₁ : Bool)
    (hTangent : c₀ ((Equiv.swap (0 : Fin 2) 1) i₀) = c₁ ((Equiv.swap (0 : Fin 2) 1) i₁))
    (hOrigin : y₀ + (if side₀ then ε else 0) • EuclideanSpace.single (c₀ i₀) (1 : ℝ) =
      y₁ + (if side₁ then ε else 0) • EuclideanSpace.single (c₁ i₁) (1 : ℝ)) :
    let other := fun j : Fin 2 => (Equiv.swap (0 : Fin 2) 1) j
    let embed := fun (c : Fin 2 ↪ Fin (n + 2)) (Y : Domain (n + 2)) (t : Domain 2) =>
      Y + t 0 • EuclideanSpace.single (c 0) (1 : ℝ) + t 1 • EuclideanSpace.single (c 1) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let edge := fun (j : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 j true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let F := fun c Y j side l s => rep l (c (other j)) (embed c Y (edge j side s))
    let f := fun c Y j side l s => w l (embed c Y (edge j side s))
    let g := fun c Y j side l s => Dw l (embed c Y (edge j side s)) (c (other j))
    let a : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => a + (ε / 2) • z
    let V := fun c Y j side (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F c Y j side (0 : Fin 2) ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F c Y j side (1 : Fin 2) ((b (T z)).1 0)
    (∀ l s, F c₀ y₀ i₀ side₀ l s = F c₁ y₁ i₁ side₁ l s) ∧
    (∀ l s, f c₀ y₀ i₀ side₀ l s = f c₁ y₁ i₁ side₁ l s) ∧
    (∀ l s, g c₀ y₀ i₀ side₀ l s = g c₁ y₁ i₁ side₁ l s) ∧
    V c₀ y₀ i₀ side₀ = V c₁ y₁ i₁ side₁ := by
  intro other embed b edge F f g a T V
  have hAxis (c : Fin 2 ↪ Fin (n + 2)) (Y : Domain (n + 2)) (j : Fin 2) (s t : ℝ) :
      embed c Y (cubicalSignedFaceIsometry 1 j true
        (b.symm (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) t))) =
        (Y + t • EuclideanSpace.single (c j) (1 : ℝ)) + s • EuclideanSpace.single (c (other j)) (1 : ℝ) := by
    have h := two_vector_square_axis Y (EuclideanSpace.single (c 0) (1 : ℝ))
      (EuclideanSpace.single (c 1) (1 : ℝ)) j (EuclideanSpace.single (0 : Fin 1) s) t
    fin_cases j <;> simpa [embed, b, other] using h
  have hPoint (s : ℝ) : embed c₀ y₀ (edge i₀ side₀ s) = embed c₁ y₁ (edge i₁ side₁ s) := by
    change embed c₀ y₀ (cubicalSignedFaceIsometry 1 i₀ true (b.symm
      (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) (if side₀ then ε else 0)))) =
      embed c₁ y₁ (cubicalSignedFaceIsometry 1 i₁ true (b.symm
        (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) (if side₁ then ε else 0))))
    rw [hAxis, hAxis, hOrigin, hTangent]
  have hF (l : Fin 2) (s : ℝ) : F c₀ y₀ i₀ side₀ l s = F c₁ y₁ i₁ side₁ l s := by
    change rep l (c₀ (other i₀)) (embed c₀ y₀ (edge i₀ side₀ s)) = _
    rw [hTangent, hPoint]
  refine ⟨hF, fun l s => congrArg (w l) (hPoint s), ?_, ?_⟩
  · intro l s
    change Dw l (embed c₀ y₀ (edge i₀ side₀ s)) (c₀ (other i₀)) = _
    rw [hTangent, hPoint]
  · funext z
    change (1 - (b (T z)).2 0 / ε) • F c₀ y₀ i₀ side₀ 0 ((b (T z)).1 0) +
      ((b (T z)).2 0 / ε) • F c₀ y₀ i₀ side₀ 1 ((b (T z)).1 0) = _
    rw [hF, hF]

/-- Two original coordinate squares with the same actual physical oriented
edge use the same global coordinate ACL representative, original edge
columns and affine vertical connector on the entire carrier. -/
theorem original_prism_common_edge_coherence {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (c₀ c₁ : Fin 2 ↪ Fin (n + 2)) (ε : ℝ) (y₀ y₁ : Domain (n + 2))
    (i₀ i₁ : Fin 2) (side₀ side₁ : Bool)
    (hTangent : c₀ ((Equiv.swap (0 : Fin 2) 1) i₀) = c₁ ((Equiv.swap (0 : Fin 2) 1) i₁))
    (hOrigin : y₀ + (if side₀ then ε else 0) • EuclideanSpace.single (c₀ i₀) (1 : ℝ) =
      y₁ + (if side₁ then ε else 0) • EuclideanSpace.single (c₁ i₁) (1 : ℝ)) :
    let rep := fun (l : Fin 2) (j : Fin (n + 2)) =>
      coordinatePermACLRepresentative (Equiv.swap (Fin.last (n + 1)) j) (-1) 1 (w l) (Dw l)
    let other := fun j : Fin 2 => (Equiv.swap (0 : Fin 2) 1) j
    let embed := fun (c : Fin 2 ↪ Fin (n + 2)) (Y : Domain (n + 2)) (t : Domain 2) =>
      Y + t 0 • EuclideanSpace.single (c 0) (1 : ℝ) + t 1 • EuclideanSpace.single (c 1) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let edge := fun (j : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 j true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let F := fun c Y j side l s => rep l (c (other j)) (embed c Y (edge j side s))
    let f := fun c Y j side l s => w l (embed c Y (edge j side s))
    let g := fun c Y j side l s => Dw l (embed c Y (edge j side s)) (c (other j))
    let a : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => a + (ε / 2) • z
    let V := fun c Y j side (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F c Y j side (0 : Fin 2) ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F c Y j side (1 : Fin 2) ((b (T z)).1 0)
    (∀ l s, F c₀ y₀ i₀ side₀ l s = F c₁ y₁ i₁ side₁ l s) ∧
    (∀ l s, f c₀ y₀ i₀ side₀ l s = f c₁ y₁ i₁ side₁ l s) ∧
    (∀ l s, g c₀ y₀ i₀ side₀ l s = g c₁ y₁ i₁ side₁ l s) ∧
    V c₀ y₀ i₀ side₀ = V c₁ y₁ i₁ side₁ := by
  intro rep other embed b edge F f g a T V
  dsimp only [F, V]
  generalize hRep : rep = R
  exact common_edge_data_of_representatives w Dw R c₀ c₁ ε y₀ y₁ i₀ i₁ side₀ side₁ hTangent hOrigin

end StratificationTheory
