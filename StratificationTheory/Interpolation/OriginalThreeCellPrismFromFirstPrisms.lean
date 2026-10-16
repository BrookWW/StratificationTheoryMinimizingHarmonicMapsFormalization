module

public import StratificationTheory.Interpolation.CubicalFourPrismAssembler
public import StratificationTheory.Foundation.ThreeCoordinatePrismSignedCapValues
public import StratificationTheory.Foundation.ThreeCoordinatePrismTimeFaceValues

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Original normalized three-face data and actual first-prism data of its
six original square facets give an actual four-dimensional prism. The
common physical lower-boundary representative and every matching endpoint
class are constructed internally from the original directional functions. -/
theorem exists_original_three_cell_prism_from_first_prisms {q : ℕ}
    {Ndim : ℕ} (w : Fin 2 → Domain Ndim → Ambient q)
    (Dw : Fin 2 → Domain Ndim → Gradient Ndim q)
    (rep : Fin 2 → Fin Ndim → Domain Ndim → Ambient q)
    (coord : Fin 3 ↪ Fin Ndim) {ε : ℝ} (hε : 0 < ε) (y : Domain Ndim)
    (V : (Fin 3 × Bool) → Domain 3 → Ambient q)
    (DV : (Fin 3 × Bool) → Domain 3 → Gradient 3 q)
    {N : Set (Ambient q)} (hN : IsCompact N)
    (C : (Fin 3 × Bool) → ℝ) :
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let U := fun side : Bool => w (if side then 1 else 0) ∘ P
    let DU := fun (side : Bool) (z : Domain 3) (k : Fin 3) =>
      (ε / 2) • Dw (if side then 1 else 0) (P z) (coord k)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
    let S := ⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain 3 := ⟨⋂ k : Fin 3, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite (fun k : Fin 3 => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain 4 := ⟨⋂ k : Fin 4, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite (fun k : Fin 4 => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let A := fun i : Fin 3 => cubicalSignedPermutation 3 (Equiv.swap (Fin.last 2) i) (fun _ => true)
    let pair := fun i : Fin 3 =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let origin := fun j : Fin 3 × Bool => y + (if j.2 then ε else 0) • EuclideanSpace.single (coord j.1) (1 : ℝ)
    let e₁ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let embed := fun (j : Fin 3 × Bool) (t : Domain 2) => origin j +
      t 0 • EuclideanSpace.single (pair j.1 0) (1 : ℝ) + t 1 • EuclideanSpace.single (pair j.1 1) (1 : ℝ)
    let edgePoint := fun (a : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 a true
      (e₁.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let edgeF := fun j a side l s => rep l (pair j.1 ((Equiv.swap (0 : Fin 2) 1) a)) (embed j (edgePoint a side s))
    let T₂ := fun z : Domain 2 => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let sourceU := fun (j : Fin 3 × Bool) (side : Bool) => w (if side then 1 else 0) ∘ embed j ∘ T₂
    let edgeV := fun j (a : Fin 2) (side : Bool) (z : Domain 2) =>
      (1 - (e₁ (T₂ z)).2 0 / ε) • edgeF j a side 0 ((e₁ (T₂ z)).1 0) +
        ((e₁ (T₂ z)).2 0 / ε) • edgeF j a side 1 ((e₁ (T₂ z)).1 0)
    let sourceFace := fun (j : Fin 3 × Bool) (k : Fin 3 × Bool) =>
      if k.1 = 0 then edgeV j 0 k.2 ∘ cubicalSignedFaceIsometry 1 0 true
      else if k.1 = 1 then edgeV j 1 k.2 else sourceU j k.2
    let F : (Fin 4 × Bool) → Domain 3 → Ambient q := fun j => Fin.lastCases (U j.2) (fun i => V (i, j.2) ∘ A i) j.1
    (∀ side, MemW12 B (U side) (DU side)) →
    (∀ side, ∀ᵐ x ∂volume.restrict B.val, U side x ∈ N) →
    (∀ j, MemW12 B (V j) (DV j)) →
    (∀ j, ∀ᵐ x ∂volume.restrict B.val, (infDist (V j x) N) ^ 2 ≤ C j) →
    ∀ KH : Bool → Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ side i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => U side (cubicalSignedFaceIsometry 2 i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        KH side i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U side (cubicalSignedFaceIsometry 2 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ side i positive,
      (KH side i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 2 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => U side (cubicalSignedFaceIsometry 2 i positive
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) →
    ∀ KV : (Fin 3 × Bool) → Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => V j (cubicalSignedFaceIsometry 2 i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        KV j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V j (cubicalSignedFaceIsometry 2 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ j i positive,
      (KV j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 2 → Ambient q)
        =ᵐ[volume.restrict S] sourceFace j (i, positive)) →
    ∃ (G : Domain 4 → Ambient q) (D : Domain 4 → Gradient 4 q),
      let W := fun z : Domain 4 => G (‖WithLp.ofLp z‖⁻¹ • z)
      (∀ j x, x ∈ B.val → G (cubicalSignedFaceIsometry 3 j.1 j.2
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = F j x) ∧
      MemW12 Ω W D ∧
      (∫ z in Ω.val, hsNormSq (D z)) ≤ 2 *
        ((∑ side : Bool, ∫ z in B.val, hsNormSq (DU side z)) +
          ∑ j : Fin 3 × Bool, ∫ z in B.val, hsNormSq (DV j z)) ∧
      (∀ᵐ z ∂volume.restrict Ω.val, (infDist (W z) N) ^ 2 ≤ ∑ j : Fin 3 × Bool, max (C j) 0) ∧
      (∃ H : Fin 4 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => W (cubicalSignedFaceIsometry 3 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (cubicalSignedFaceIsometry 3 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i positive,
          (H i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 3 → Ambient q)
            =ᵐ[volume.restrict B.val] F (i, positive)) ∧
      ∀ P : Ambient q → Prop,
        (∀ side, ∀ᵐ z ∂volume.restrict B.val, P (U side z)) →
        (∀ j, ∀ᵐ z ∂volume.restrict B.val, P (V j z)) →
        ∀ᵐ z ∂volume.restrict Ω.val, P (W z) := by
  intro P U DU b e S B Ω A pair origin e₁ embed edgePoint edgeF T₂ sourceU edgeV sourceFace F
    hU hTarget hV hDist KH hKH hKHEnd KV hKV hKVEnd
  let free := fun z : Domain 3 => if |z 0| < 1 then (0 : Fin 3) else if |z 1| < 1 then 1 else 2
  let E := fun z : Domain 4 =>
    let sp : Domain 3 := WithLp.toLp 2 ![z 0, z 1, z 2]
    if z 3 = -1 then w 0 (P sp) else if z 3 = 1 then w 1 (P sp) else
      (1 - (z 3 + 1) / 2) • rep 0 (coord (free sp)) (P sp) +
        ((z 3 + 1) / 2) • rep 1 (coord (free sp)) (P sp)
  have hTime (side : Bool) (z : Domain 3) :
      E (cubicalSignedFaceIsometry 3 (3 : Fin 4) side
        (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = U side z :=
    three_coordinate_prism_time_face_values w rep coord ε y side z
  have hEnd j i (positive : Bool) :
      (KV j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 2 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (cubicalSignedFaceIsometry 3 j.1.castSucc j.2 (e.symm
          (A j.1 (cubicalSignedFaceIsometry 2 i positive (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1))),
            EuclideanSpace.single (0 : Fin 1) 1)))) := by
    filter_upwards [hKVEnd j i positive, ae_restrict_mem (isOpen_iInter_of_finite
      (fun k : Fin 2 => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)).measurableSet] with x hx hxB
    have hPoint := three_coordinate_prism_signed_cap_values w rep coord hε y j.1 j.2 (i, positive) x hxB
    with_reducible exact hx.trans hPoint.symm
  exact exists_cubical_four_prism_filling U DU V DV E hN C hU hTarget hV hDist hTime
    KH hKH hKHEnd KV hKV hEnd

end StratificationTheory
