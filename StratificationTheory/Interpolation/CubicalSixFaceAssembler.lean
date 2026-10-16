module

public import StratificationTheory.Foundation.CubicalFaceFamilyExtension
public import StratificationTheory.Foundation.CubicalThreeDimensionalIncidence
public import StratificationTheory.Foundation.UnitSquareCoordinateSwap

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Two original horizontal squares and four actual vertical edge
connectors, with their original physical edge classes, produce one genuine
three-dimensional weak filling and all six original face traces. -/
theorem exists_cubical_six_face_filling {q : ℕ}
    (U : Bool → Domain 2 → Ambient q) (DU : Bool → Domain 2 → Gradient 2 q)
    (V : Fin 2 → Bool → Domain 2 → Ambient q) (DV : Fin 2 → Bool → Domain 2 → Gradient 2 q)
    (E : Domain 3 → Ambient q) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let S := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω : OpenDomain 3 :=
      ⟨⋂ k : Fin 3, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin 3 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let A := cubicalSignedFaceIsometry 1 (0 : Fin 2) true
    let F : (Fin 3 × Bool) → Domain 2 → Ambient q := fun j =>
      if j.1 = 0 then V 0 j.2 ∘ A else if j.1 = 1 then V 1 j.2 else U j.2
    (∀ side, MemW12 B (U side) (DU side)) →
    (∀ i side, MemW12 B (V i side) (DV i side)) →
    ∀ Bnd : ℝ, (∀ side, ∀ᵐ x ∂volume.restrict B.val, ‖U side x‖ ≤ Bnd) →
    (∀ i side, ∀ᵐ x ∂volume.restrict B.val, ‖V i side x‖ ≤ Bnd) →
    ∀ (KH : Bool → Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)))
      (HT HS : Fin 2 → Bool → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S))),
    (∀ side i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain 1 => U side (cubicalSignedFaceIsometry 1 i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        KH side i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U side (cubicalSignedFaceIsometry 1 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ i side, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain 1 => V i side (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S),
        HT i side ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V i side (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ i side, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain 1 => V i side (b.symm (EuclideanSpace.single (0 : Fin 1) t, x))) 2 (volume.restrict S),
        HS i side ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V i side (b.symm (EuclideanSpace.single (0 : Fin 1) t, x)))) →
    (∀ side i (positive : Bool),
      (KH side i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 1 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (if i = 0 then
          WithLp.toLp 2 ![if positive then 1 else -1, x 0, if side then 1 else -1]
          else WithLp.toLp 2 ![x 0, if positive then 1 else -1, if side then 1 else -1]))) →
    (∀ i side (positive : Bool),
      (HT i side ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 1 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (if i = 0 then
          WithLp.toLp 2 ![if side then 1 else -1, x 0, if positive then 1 else -1]
          else WithLp.toLp 2 ![x 0, if side then 1 else -1, if positive then 1 else -1]))) →
    (∀ i side (positive : Bool),
      (HS i side ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 1 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (if i = 0 then
          WithLp.toLp 2 ![if side then 1 else -1, if positive then 1 else -1, x 0]
          else WithLp.toLp 2 ![if positive then 1 else -1, if side then 1 else -1, x 0]))) →
    ∃ (G : Domain 3 → Ambient q) (D : Domain 3 → Gradient 3 q),
      let W : Domain 3 → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
      (∀ j x, x ∈ B.val → G (cubicalSignedFaceIsometry 2 j.1 j.2
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = F j x) ∧
      MemW12 Ω W D ∧
      (∫ y in Ω.val, hsNormSq (D y)) ≤ 3 *
        ((∑ side : Bool, ∫ x in B.val, hsNormSq (DU side x)) +
          ∑ i : Fin 2, ∑ side : Bool, ∫ x in B.val, hsNormSq (DV i side x)) ∧
      (∃ H : Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain 2 => W (cubicalSignedFaceIsometry 2 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (cubicalSignedFaceIsometry 2 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i positive,
          (H i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 2 → Ambient q)
            =ᵐ[volume.restrict B.val] F (i, positive)) ∧
      ∀ P : Ambient q → Prop,
        (∀ side, ∀ᵐ x ∂volume.restrict B.val, P (U side x)) →
        (∀ i side, ∀ᵐ x ∂volume.restrict B.val, P (V i side x)) →
        ∀ᵐ y ∂volume.restrict Ω.val, P (W y) := by
  classical
  intro b e B S Ω A F hU hV Bnd hBU hBV KH HT HS hKH hHT hHS hEH hET hES
  have hSwap (side : Bool) := memW12_unit_square_swap_energy (V 0 side) (DV 0 side) (hV 0 side)
  let DF : (Fin 3 × Bool) → Domain 2 → Gradient 2 q := fun j =>
    if j.1 = 0 then (fun y i => if i = 0 then DV 0 j.2 (A y) 1 else DV 0 j.2 (A y) 0)
    else if j.1 = 1 then DV 1 j.2 else DU j.2
  have hFace (j : Fin 3 × Bool) : MemW12 B (F j) (DF j) := by
    rcases j with ⟨j, side⟩
    fin_cases j
    · exact (hSwap side).1
    · exact hV 1 side
    · exact hU side
  have hBound (j : Fin 3 × Bool) : ∀ᵐ x ∂volume.restrict B.val, ‖F j x‖ ≤ Bnd := by
    rcases j with ⟨j, side⟩
    fin_cases j
    · exact (hSwap side).2.2 (fun z => ‖z‖ ≤ Bnd) (hBV 0 side)
    · exact hBV 1 side
    · exact hBU side
  let K : (Fin 3 × Bool) → Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)) :=
    fun j i => if j.1 = 0 then (if i = 0 then HT 0 j.2 else HS 0 j.2)
      else if j.1 = 1 then (if i = 0 then HS 1 j.2 else HT 1 j.2) else KH j.2 i
  have hLast : cubicalSignedFaceIsometry 1 (1 : Fin 2) true = LinearIsometryEquiv.refl ℝ (Domain 2) := by
    apply LinearIsometryEquiv.ext
    intro y
    ext k
    rw [cubicalSignedFaceIsometry_coordinate, show Fin.last 1 = (1 : Fin 2) by decide]
    simp only [Equiv.swap_self, Equiv.refl_apply, ite_true]
    split_ifs with hk
    · rw [hk]
      rfl
    · rfl
  let Raw := fun (g : Domain 2 → Ambient q)
    (H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S))) =>
    ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain 1 => g (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => g (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
  have hNative (x : Domain 1) (t : ℝ) : A (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
      b.symm (EuclideanSpace.single (0 : Fin 1) t, x) := unit_square_coordinate_swap.2 x t
  have hSRaw (i : Fin 2) (side : Bool) : Raw (V i side ∘ A) (HS i side) := by
    simpa only [Raw, Function.comp_apply, hNative] using hHS i side
  have hRaw (j : Fin 3 × Bool) (i : Fin 2) : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain 1 => F j (cubicalSignedFaceIsometry 1 i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F j (cubicalSignedFaceIsometry 1 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
    rcases j with ⟨j, side⟩
    fin_cases j <;> fin_cases i
    · change Raw (fun y => V 0 side (A (A y))) (HT 0 side)
      have hFn : (fun y => V 0 side (A (A y))) = V 0 side :=
        funext fun y => congrArg (V 0 side) (unit_square_coordinate_swap.1 y).2.2
      rw [hFn]
      exact hHT 0 side
    · change Raw (fun y => V 0 side (A (cubicalSignedFaceIsometry 1 (1 : Fin 2) true y))) (HS 0 side)
      rw [hLast]
      exact hSRaw 0 side
    · change Raw (V 1 side ∘ A) (HS 1 side)
      exact hSRaw 1 side
    · change Raw (fun y => V 1 side (cubicalSignedFaceIsometry 1 (1 : Fin 2) true y)) (HT 1 side)
      rw [hLast]
      exact hHT 1 side
    · exact hKH side 0
    · exact hKH side 1
  have hEnd (j : Fin 3 × Bool) (i : Fin 2) (positive : Bool) :
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 1 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (cubicalSignedFaceIsometry 2 j.1 j.2 (e.symm
          (cubicalSignedFaceIsometry 1 i positive (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1)))) := by
    rcases j with ⟨j, side⟩
    fin_cases j <;> fin_cases i <;> norm_num only [K]
    · filter_upwards [hET 0 side positive] with x hx
      exact hx.trans (congrArg E (cubical_three_dimensional_edge_charts side positive x).1.symm)
    · filter_upwards [hES 0 side positive] with x hx
      exact hx.trans (congrArg E (cubical_three_dimensional_edge_charts side positive x).2.1.symm)
    · filter_upwards [hES 1 side positive] with x hx
      exact hx.trans (congrArg E (cubical_three_dimensional_edge_charts side positive x).2.2.1.symm)
    · filter_upwards [hET 1 side positive] with x hx
      exact hx.trans (congrArg E (cubical_three_dimensional_edge_charts side positive x).2.2.2.1.symm)
    · filter_upwards [hEH side 0 positive] with x hx
      exact hx.trans (congrArg E (cubical_three_dimensional_edge_charts side positive x).2.2.2.2.1.symm)
    · filter_upwards [hEH side 1 positive] with x hx
      exact hx.trans (congrArg E (cubical_three_dimensional_edge_charts side positive x).2.2.2.2.2.symm)
  obtain ⟨G, D, hCap, hW, _hExact, hEnergy, hTrace, hProp⟩ :=
    exists_cubical_face_family_extension (n := 0) F DF E hFace Bnd hBound K hRaw hEnd
  have hSum : (∑ j : Fin 3 × Bool, ∫ x in B.val, hsNormSq (DF j x)) =
      (∑ side : Bool, ∫ x in B.val, hsNormSq (DU side x)) +
        ∑ i : Fin 2, ∑ side : Bool, ∫ x in B.val, hsNormSq (DV i side x) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    have hSwapE (side : Bool) :
        (∫ x in B.val, hsNormSq (fun i => if i = 0 then DV 0 side (A x) 1 else DV 0 side (A x) 0)) =
          ∫ x in B.val, hsNormSq (DV 0 side x) := (hSwap side).2.1
    change (∑ side : Bool, ∫ x in B.val, hsNormSq (fun i => if i = 0 then DV 0 side (A x) 1 else DV 0 side (A x) 0)) +
      (∑ side : Bool, ∫ x in B.val, hsNormSq (DV 1 side x)) +
      (∑ side : Bool, ∫ x in B.val, hsNormSq (DU side x)) = _
    rw [Finset.sum_congr rfl (fun side _ => hSwapE side)]
    rw [Fin.sum_univ_two]
    ring
  refine ⟨G, D, hCap, hW, ?_, hTrace, ?_⟩
  · change (∫ y in Ω.val, hsNormSq (D y)) ≤
      (((2 : ℝ) + 1) / ((2 : ℝ) - 1)) * (∑ j : Fin 3 × Bool, ∫ x in B.val, hsNormSq (DF j x)) at hEnergy
    rw [show (((2 : ℝ) + 1) / ((2 : ℝ) - 1)) = 3 by norm_num, hSum] at hEnergy
    exact hEnergy
  · intro P hPU hPV
    apply hProp P
    intro j
    rcases j with ⟨j, side⟩
    fin_cases j
    · exact (hSwap side).2.2 P (hPV 0 side)
    · exact hPV 1 side
    · exact hPU side

end StratificationTheory
