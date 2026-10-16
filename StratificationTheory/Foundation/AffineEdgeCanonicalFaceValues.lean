module

public import StratificationTheory.Foundation.UnitSquareCoordinateSwap
public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

public section

open HarmonicMaps

namespace StratificationTheory

/-- The actual normalized affine edge connector in its canonical spatial
face chart has exactly the original free spatial parameter and original
affine time coefficient. -/
theorem affine_edge_canonical_face_value {q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : Fin 2 → Bool → Fin 2 → ℝ → Ambient q) (a : Fin 2) (side : Bool) (x : Domain 2) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let T := fun z : Domain 2 => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let V := fun (k : Fin 2) (positive : Bool) (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F k positive 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F k positive 1 ((b (T z)).1 0)
    V a side (cubicalSignedFaceIsometry 1 a true x) =
      (1 - (x a + 1) / 2) • F a side 0 (ε / 2 + (ε / 2) * x ((Equiv.swap (0 : Fin 2) 1) a)) +
        ((x a + 1) / 2) • F a side 1 (ε / 2 + (ε / 2) * x ((Equiv.swap (0 : Fin 2) 1) a)) := by
  intro b T V
  have hTau (r : ℝ) : (ε / 2 + (ε / 2) * r) / ε = (r + 1) / 2 := by
    field_simp [hε.ne']
    ring
  have hCoordinates (k : Fin 2) (z : Domain 2) :
      cubicalSignedFaceIsometry 1 k true z 0 = z ((Equiv.swap (0 : Fin 2) 1) k) ∧
      cubicalSignedFaceIsometry 1 k true z 1 = z k := by
    fin_cases k
    · exact ⟨(unit_square_coordinate_swap.1 z).1, (unit_square_coordinate_swap.1 z).2.1⟩
    · change cubicalSignedFaceIsometry 1 (1 : Fin 2) true z 0 = z 0 ∧
        cubicalSignedFaceIsometry 1 (1 : Fin 2) true z 1 = z 1
      constructor <;> simp [cubicalSignedFaceIsometry_coordinate]
  change (1 - (ε / 2 + (ε / 2) * (cubicalSignedFaceIsometry 1 a true x) 1) / ε) •
      F a side 0 (ε / 2 + (ε / 2) * (cubicalSignedFaceIsometry 1 a true x) 0) +
        ((ε / 2 + (ε / 2) * (cubicalSignedFaceIsometry 1 a true x) 1) / ε) •
          F a side 1 (ε / 2 + (ε / 2) * (cubicalSignedFaceIsometry 1 a true x) 0) = _
  rw [(hCoordinates a x).1, (hCoordinates a x).2, hTau]

end StratificationTheory
