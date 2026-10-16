module

public import StratificationTheory.Foundation.TwoCoordinateSquareGeometry
public import StratificationTheory.Foundation.CoordinateTraceRestrictions

/-!
# Original native square traces in two-vector coordinates

The original raw affine source slices and their endpoint classes are the
literal native coordinate slices of the same two-vector square. Every L2
class is transported by the corresponding whole-carrier point equality.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The same continuous native curves represent the raw coordinate
restrictions of the original two-vector square at both closed ends. -/
theorem two_vector_square_original_trace_transport {N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w : Fin 2 → Domain N → Ambient q) (y : Domain N) (v : Fin 2 → Domain N) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let S := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let δ := fun positive : Bool => if positive then ε else 0
    let other := fun i : Fin 2 => (Equiv.swap (0 : Fin 2) 1) i
    let u := fun (l : Fin 2) (z : Domain 2) => w l (y + z 0 • v 0 + z 1 • v 1)
    let edgePoint := fun (i : Fin 2) (positive : Bool) (s : ℝ) =>
      cubicalSignedFaceIsometry 1 i true (b.symm
        (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) (δ positive)))
    ∀ H : Fin 2 → Fin 2 → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x : Domain 1 => w l (y + x 0 • v (other i) + t • v i))
        2 (volume.restrict S),
        H l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
          (fun x : Domain 1 => w l (y + x 0 • v (other i) + t • v i))) →
    (∀ l i positive,
      ∃ hs : MemLp (fun x : Domain 1 => w l (y + δ positive • v i + x 0 • v (other i)))
        2 (volume.restrict S),
        H l i ⟨δ positive, by cases positive <;> simp [δ, hε.le],
          by cases positive <;> simp [δ, hε.le]⟩ = hs.toLp
          (fun x : Domain 1 => w l (y + δ positive • v i + x 0 • v (other i)))) →
    (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x : Domain 1 => u l (cubicalSignedFaceIsometry 1 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        H l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x : Domain 1 => u l
          (cubicalSignedFaceIsometry 1 i true (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
    ∀ l i positive,
      ∃ hs : MemLp (fun x : Domain 1 => u l (edgePoint i positive (x 0))) 2 (volume.restrict S),
        H l i ⟨δ positive, by cases positive <;> simp [δ, hε.le],
          by cases positive <;> simp [δ, hε.le]⟩ = hs.toLp
          (fun x : Domain 1 => u l (edgePoint i positive (x 0))) := by
  intro b S δ other u edgePoint H hH hEnd
  have hAxis (l i : Fin 2) (x : Domain 1) (t : ℝ) :
      u l (cubicalSignedFaceIsometry 1 i true (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) =
        w l (y + t • v i + x 0 • v (other i)) := by
    apply congrArg (w l)
    have h := two_vector_square_axis y (v 0) (v 1) i x t
    fin_cases i <;> simpa [b, other] using h
  constructor
  · intro l i
    filter_upwards [hH l i] with t ht htI
    obtain ⟨hs, heq⟩ := ht htI
    have hAE : (fun x : Domain 1 => w l (y + x 0 • v (other i) + t • v i)) =ᵐ[volume.restrict S]
        (fun x => u l (cubicalSignedFaceIsometry 1 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
      apply Eventually.of_forall
      intro x
      change w l (y + x 0 • v (other i) + t • v i) =
        u l (cubicalSignedFaceIsometry 1 i true (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
      rw [hAxis]
      congr 1
      abel
    have hnew := hs.ae_eq hAE
    exact ⟨hnew, heq.trans (hs.toLp_congr hnew hAE)⟩
  · intro l i positive
    obtain ⟨hs, heq⟩ := hEnd l i positive
    have hAE : (fun x : Domain 1 => w l (y + δ positive • v i + x 0 • v (other i))) =ᵐ[volume.restrict S]
        (fun x => u l (edgePoint i positive (x 0))) := by
      apply Eventually.of_forall
      intro x
      exact (hAxis l i (EuclideanSpace.single 0 (x 0)) (δ positive)).symm
    have hnew := hs.ae_eq hAE
    exact ⟨hnew, heq.trans (hs.toLp_congr hnew hAE)⟩

end StratificationTheory
