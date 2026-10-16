module

public import StratificationTheory.Foundation.CoordinateGridCompatibility
public import StratificationTheory.Foundation.TwoVectorSquareTraceTransport

public section

open HarmonicMaps

namespace StratificationTheory

private theorem spatial_face_selector {q : ℕ}
    (V : Fin 2 → Bool → Domain 2 → Ambient q) (U : Bool → Domain 2 → Ambient q)
    (Q : Domain 2 ≃ₗᵢ[ℝ] Domain 2) (i : Fin 2) (side : Bool) :
    (if i.castSucc = (0 : Fin 3) then V 0 side ∘ Q
      else if i.castSucc = (1 : Fin 3) then V 1 side else U side) =
      if i = 0 then V i side ∘ Q else V i side := by
  fin_cases i <;> rfl

private theorem prism_spatial_face_coherence_of_representatives {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (rep : Fin 2 → Fin 2 → Domain (n + 2) → Ambient q)
    (coord : Fin 2 ↪ Fin (n + 2)) (ε : ℝ) (y : Domain (n + 2)) (i : Fin 2) :
    let vec := fun j : Fin 2 => EuclideanSpace.single (coord j) (1 : ℝ)
    let other := fun j : Fin 2 => (Equiv.swap (0 : Fin 2) 1) j
    let embed := fun (Y : Domain (n + 2)) (t : Domain 2) => Y + t 0 • vec 0 + t 1 • vec 1
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let edge := fun (j : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 j true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let F := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
      rep l (other j) (embed Y (edge j side s))
    let f := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
      w l (embed Y (edge j side s))
    let g := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
      Dw l (embed Y (edge j side s)) (coord (other j))
    let a : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => a + (ε / 2) • z
    let V := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F Y j side 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F Y j side 1 ((b (T z)).1 0)
    let U := fun (Y : Domain (n + 2)) (side : Bool) (z : Domain 2) =>
      w (if side then (1 : Fin 2) else 0) (embed Y (T z))
    let Q := cubicalSignedFaceIsometry 1 (0 : Fin 2) true
    let face := fun (Y : Domain (n + 2)) (j : Fin 3 × Bool) =>
      if j.1 = 0 then V Y 0 j.2 ∘ Q else if j.1 = 1 then V Y 1 j.2 else U Y j.2
    (∀ l s, F y i true l s = F (y + ε • vec i) i false l s) ∧
    (∀ l s, f y i true l s = f (y + ε • vec i) i false l s) ∧
    (∀ l s, g y i true l s = g (y + ε • vec i) i false l s) ∧
    V y i true = V (y + ε • vec i) i false ∧
    face y (i.castSucc, true) = face (y + ε • vec i) (i.castSucc, false) := by
  intro vec other embed b edge F f g a T V U Q face
  have hAxis (Y : Domain (n + 2)) (j : Fin 2) (s t : ℝ) :
      embed Y (cubicalSignedFaceIsometry 1 j true
        (b.symm (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) t))) =
        (Y + t • vec j) + s • vec (other j) := by
    have h := two_vector_square_axis Y (vec 0) (vec 1) j (EuclideanSpace.single (0 : Fin 1) s) t
    fin_cases j <;> simpa [embed, b, other] using h
  have hPoint (s : ℝ) : embed y (edge i true s) = embed (y + ε • vec i) (edge i false s) := by
    change embed y (cubicalSignedFaceIsometry 1 i true (b.symm
      (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) ε))) =
      embed (y + ε • vec i) (cubicalSignedFaceIsometry 1 i true (b.symm
        (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) 0)))
    rw [hAxis, hAxis, zero_smul, add_zero]
  have hF (l : Fin 2) (s : ℝ) : F y i true l s = F (y + ε • vec i) i false l s :=
    congrArg (rep l (other i)) (hPoint s)
  have hf (l : Fin 2) (s : ℝ) : f y i true l s = f (y + ε • vec i) i false l s :=
    congrArg (w l) (hPoint s)
  have hg (l : Fin 2) (s : ℝ) : g y i true l s = g (y + ε • vec i) i false l s :=
    congrArg (fun x => Dw l x (coord (other i))) (hPoint s)
  have hV : V y i true = V (y + ε • vec i) i false := by
    funext z
    change (1 - (b (T z)).2 0 / ε) • F y i true 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F y i true 1 ((b (T z)).1 0) = _
    rw [hF, hF]
  refine ⟨hF, hf, hg, hV, ?_⟩
  change (if i.castSucc = (0 : Fin 3) then V y 0 true ∘ Q
      else if i.castSucc = (1 : Fin 3) then V y 1 true else U y true) =
    (if i.castSucc = (0 : Fin 3) then V (y + ε • vec i) 0 false ∘ Q
      else if i.castSucc = (1 : Fin 3) then V (y + ε • vec i) 1 false else U (y + ε • vec i) false)
  generalize hVy : V y = Vy at hV ⊢
  generalize hVz : V (y + ε • vec i) = Vz at hV ⊢
  generalize hUy : U y = Uy at ⊢
  generalize hUz : U (y + ε • vec i) = Uz at ⊢
  calc
    _ = (if i = 0 then Vy i true ∘ Q else Vy i true) :=
      spatial_face_selector Vy Uy Q i true
    _ = (if i = 0 then Vz i false ∘ Q else Vz i false) :=
      congrArg (fun v : Domain 2 → Ambient q => if i = 0 then v ∘ Q else v) hV
    _ = _ := (spatial_face_selector Vz Uz Q i false).symm


/-- Neighboring original prism cells use exactly the same original global
line representative, raw edge map, raw edge columns and actual affine
vertical face. Their canonical shared signed-face maps therefore agree on
the entire original unit-face carrier. -/
theorem original_prism_spatial_face_coherence {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (coord : Fin 2 ↪ Fin (n + 2)) (ε : ℝ) (y : Domain (n + 2)) (i : Fin 2) :
    let vec := fun j : Fin 2 => EuclideanSpace.single (coord j) (1 : ℝ)
    let p := fun j : Fin 2 => Equiv.swap (Fin.last (n + 1)) (coord j)
    let other := fun j : Fin 2 => (Equiv.swap (0 : Fin 2) 1) j
    let rep := fun (l : Fin 2) (j : Fin 2) => coordinatePermACLRepresentative (p j) (-1) 1 (w l) (Dw l)
    let embed := fun (Y : Domain (n + 2)) (t : Domain 2) => Y + t 0 • vec 0 + t 1 • vec 1
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let edge := fun (j : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 j true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let F := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
      rep l (other j) (embed Y (edge j side s))
    let f := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
      w l (embed Y (edge j side s))
    let g := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
      Dw l (embed Y (edge j side s)) (coord (other j))
    let a : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => a + (ε / 2) • z
    let V := fun (Y : Domain (n + 2)) (j : Fin 2) (side : Bool) (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F Y j side 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F Y j side 1 ((b (T z)).1 0)
    let U := fun (Y : Domain (n + 2)) (side : Bool) (z : Domain 2) =>
      w (if side then (1 : Fin 2) else 0) (embed Y (T z))
    let Q := cubicalSignedFaceIsometry 1 (0 : Fin 2) true
    let face := fun (Y : Domain (n + 2)) (j : Fin 3 × Bool) =>
      if j.1 = 0 then V Y 0 j.2 ∘ Q else if j.1 = 1 then V Y 1 j.2 else U Y j.2
    (∀ l s, F y i true l s = F (y + ε • vec i) i false l s) ∧
    (∀ l s, f y i true l s = f (y + ε • vec i) i false l s) ∧
    (∀ l s, g y i true l s = g (y + ε • vec i) i false l s) ∧
    V y i true = V (y + ε • vec i) i false ∧
    face y (i.castSucc, true) = face (y + ε • vec i) (i.castSucc, false) := by
  intro vec p other rep embed b edge F f g a T V U Q face
  dsimp only [F, V, face]
  generalize hRep : rep = R
  exact prism_spatial_face_coherence_of_representatives w Dw R coord ε y i

end StratificationTheory
