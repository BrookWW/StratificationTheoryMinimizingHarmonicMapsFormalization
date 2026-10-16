module

public import StratificationTheory.Foundation.CoordinateCellNativeSlices

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The original native coordinate-face graph and raw coordinate curves
produce the same unit graph and all original native signed-face classes. -/
theorem original_coordinate_face_unit_data {d N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w : Fin 2 → Domain N → Ambient q) (Dw : Fin 2 → Domain N → Gradient N q)
    (coord : Fin (d + 1) ↪ Fin N) (y : Domain N) {Ktarget : Set (Ambient q)} :
    let P : OpenDomain (d + 1) := ⟨⋂ j : Fin (d + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
      isOpen_iInter_of_finite fun j : Fin (d + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let B : OpenDomain (d + 1) := ⟨⋂ j : Fin (d + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun j : Fin (d + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let S := ⋂ j : Fin d, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let C := ⋂ j : Fin d, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let pair := fun i : Fin (d + 1) =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last d) i).toEmbedding).trans coord
    let source := fun z : Domain (d + 1) => y + ∑ j : Fin (d + 1), z j • EuclideanSpace.single (coord j) (1 : ℝ)
    let u := fun l => w l ∘ source
    let Du := fun l z j => Dw l (source z) (coord j)
    let T := fun z : Domain (d + 1) => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let U := fun l => u l ∘ T
    let DU := fun l z j => (ε / 2) • Du l (T z) j
    let F := fun l i (x : Domain d) (t : ℝ) => w l
      (y + ∑ j : Fin d, x j • EuclideanSpace.single (pair i j) (1 : ℝ) +
        t • EuclideanSpace.single (coord i) (1 : ℝ))
    (∀ l, MemW12 P (u l) (Du l)) →
    (∀ l, ∀ᵐ z ∂volume.restrict P.val, u l z ∈ Ktarget) →
    ∀ H : Fin 2 → Fin (d + 1) → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => F l i x t) 2 (volume.restrict S),
        H l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F l i x t)) →
    (∀ l i (positive : Bool),
      ∃ hs : MemLp (fun x => F l i x (if positive then ε else 0)) 2 (volume.restrict S),
        H l i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
          by cases positive <;> simp [hε.le]⟩ = hs.toLp (fun x => F l i x (if positive then ε else 0))) →
    (∀ l, MemW12 B (U l) (DU l)) ∧
    (∀ l, (∫ z in B.val, hsNormSq (DU l z)) =
      (ε / 2) ^ ((2 : ℤ) - (d + 1 : ℕ)) * ∫ z in P.val, hsNormSq (Du l z)) ∧
    (∀ l, ∀ᵐ z ∂volume.restrict B.val, U l z ∈ Ktarget) ∧
    ∃ Kh : Fin 2 → Fin (d + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry d i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          Kh l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U l
            (cubicalSignedFaceIsometry d i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ l i (positive : Bool),
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry d i positive
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C),
          Kh l i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
            by cases positive <;> norm_num⟩ = hs.toLp (fun x => U l
              (cubicalSignedFaceIsometry d i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro P B S C e pair source u Du T U DU F hSob hTarget H hH hEnd
  have hNorm (l : Fin 2) := memW12_unit_cube_normalization_energy hε (hSob l)
  have hUnit : ∀ l, MemW12 B (U l) (DU l) := fun l => (hNorm l).1
  have hEnergy (l : Fin 2) : (∫ z in B.val, hsNormSq (DU l z)) =
      (ε / 2) ^ ((2 : ℤ) - (d + 1 : ℕ)) * ∫ z in P.val, hsNormSq (Du l z) := by
    exact (hNorm l).2.1
  have hValue (l : Fin 2) : ∀ᵐ z ∂volume.restrict B.val, U l z ∈ Ktarget :=
    (hNorm l).2.2.2 (fun z => z ∈ Ktarget) (hTarget l)
  have hPhysical (l : Fin 2) := coordinate_cell_original_trace_transport hε (w l) coord y
    (H l) (hH l) (hEnd l)
  have hUnitCurves (l : Fin 2) := exists_unit_cube_coordinate_traces hε (u l) (H l)
    (hPhysical l).1 (hPhysical l).2
  choose Kh hKh hKhEnd using hUnitCurves
  exact ⟨hUnit, hEnergy, hValue, Kh, hKh, hKhEnd⟩

end StratificationTheory
