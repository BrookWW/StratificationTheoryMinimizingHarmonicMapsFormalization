module

public import StratificationTheory.Interpolation.OriginalAllFacePrismGrid
public import StratificationTheory.Foundation.CoordinateCellNativeSlices

/-! # Original three-dimensional source faces in the unit cube chart -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The same original native three-face graph and raw coordinate curves
produce its literal unit graph and all six original square trace classes. -/
theorem original_three_face_unit_data {N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w : Fin 2 → Domain N → Ambient q) (Dw : Fin 2 → Domain N → Gradient N q)
    (coord : Fin 3 ↪ Fin N) (y : Domain N) {Ktarget : Set (Ambient q)} :
    let P : OpenDomain 3 := ⟨⋂ j : Fin 3, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
      isOpen_iInter_of_finite fun j : Fin 3 => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let B : OpenDomain 3 := ⟨⋂ j : Fin 3, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun j : Fin 3 => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let S := ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let C := ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let pair := fun i : Fin 3 =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let source := fun z : Domain 3 => y + ∑ j : Fin 3, z j • EuclideanSpace.single (coord j) (1 : ℝ)
    let u := fun l => w l ∘ source
    let Du := fun l z j => Dw l (source z) (coord j)
    let T := fun z : Domain 3 => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let U := fun l => u l ∘ T
    let DU := fun l z j => (ε / 2) • Du l (T z) j
    let F := fun l i (x : Domain 2) (t : ℝ) => w l
      (y + ∑ j : Fin 2, x j • EuclideanSpace.single (pair i j) (1 : ℝ) +
        t • EuclideanSpace.single (coord i) (1 : ℝ))
    (∀ l, MemW12 P (u l) (Du l)) →
    (∀ l, ∀ᵐ z ∂volume.restrict P.val, u l z ∈ Ktarget) →
    ∀ H : Fin 2 → Fin 3 → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => F l i x t) 2 (volume.restrict S),
        H l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F l i x t)) →
    (∀ l i (positive : Bool),
      ∃ hs : MemLp (fun x => F l i x (if positive then ε else 0)) 2 (volume.restrict S),
        H l i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
          by cases positive <;> simp [hε.le]⟩ = hs.toLp (fun x => F l i x (if positive then ε else 0))) →
    (∀ l, MemW12 B (U l) (DU l)) ∧
    (∀ l, (∫ z in B.val, hsNormSq (DU l z)) =
      (ε / 2)⁻¹ * ∫ z in P.val, hsNormSq (Du l z)) ∧
    (∀ l, ∀ᵐ z ∂volume.restrict B.val, U l z ∈ Ktarget) ∧
    ∃ Kh : Fin 2 → Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry 2 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          Kh l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U l
            (cubicalSignedFaceIsometry 2 i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ l i (positive : Bool),
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry 2 i positive
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C),
          Kh l i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
            by cases positive <;> norm_num⟩ = hs.toLp (fun x => U l
              (cubicalSignedFaceIsometry 2 i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro P B S C e pair source u Du T U DU F hSob hTarget H hH hEnd
  have hNorm (l : Fin 2) := memW12_unit_cube_normalization_energy hε (hSob l)
  have hUnit : ∀ l, MemW12 B (U l) (DU l) := fun l => (hNorm l).1
  have hEnergy (l : Fin 2) : (∫ z in B.val, hsNormSq (DU l z)) =
      (ε / 2)⁻¹ * ∫ z in P.val, hsNormSq (Du l z) := by
    simpa only [Nat.cast_ofNat, show (2 : ℤ) - (3 : ℤ) = -1 by omega, zpow_neg_one] using (hNorm l).2.1
  have hValue (l : Fin 2) : ∀ᵐ z ∂volume.restrict B.val, U l z ∈ Ktarget :=
    (hNorm l).2.2.2 (fun z => z ∈ Ktarget) (hTarget l)
  have hPhysical (l : Fin 2) := coordinate_cell_original_trace_transport hε (w l) coord y
    (H l) (hH l) (hEnd l)
  have hUnitCurves (l : Fin 2) := exists_unit_cube_coordinate_traces hε (u l) (H l)
    (hPhysical l).1 (hPhysical l).2
  choose Kh hKh hKhEnd using hUnitCurves
  exact ⟨hUnit, hEnergy, hValue, Kh, hKh, hKhEnd⟩

end StratificationTheory
