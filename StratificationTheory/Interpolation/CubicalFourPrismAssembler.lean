module

public import StratificationTheory.Foundation.CubicalFaceFamilyExtension
public import StratificationTheory.Foundation.CubicalSignedReordering
public import StratificationTheory.Foundation.ThreePrismSpacetimeFacetCoordinates
public import StratificationTheory.Foundation.CompactDistanceNormBound

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Two original three-dimensional caps and six actual first-prism faces
with their original physical endpoint classes produce one four-dimensional
cube filling. Compact-target distance bounds supply the new common norm
bound internally. All face coordinate exchanges, new weak columns and
complete boundary curves are produced by the proof. -/
theorem exists_cubical_four_prism_filling {q : ℕ}
    (U : Bool → Domain 3 → Ambient q) (DU : Bool → Domain 3 → Gradient 3 q)
    (V : (Fin 3 × Bool) → Domain 3 → Ambient q)
    (DV : (Fin 3 × Bool) → Domain 3 → Gradient 3 q)
    (E : Domain 4 → Ambient q) {N : Set (Ambient q)} (hN : IsCompact N)
    (C : (Fin 3 × Bool) → ℝ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
    let S := ⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain 3 := ⟨⋂ k : Fin 3, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite (fun k : Fin 3 => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain 4 := ⟨⋂ k : Fin 4, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite (fun k : Fin 4 => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let A := fun i : Fin 3 => cubicalSignedPermutation 3 (Equiv.swap (Fin.last 2) i) (fun _ => true)
    let facet := fun (j : Fin 3 × Bool) (z : Domain 3) => cubicalSignedFaceIsometry 3 j.1.castSucc j.2
      (e.symm (A j.1 z, EuclideanSpace.single (0 : Fin 1) 1))
    let F : (Fin 4 × Bool) → Domain 3 → Ambient q := fun j => Fin.lastCases (U j.2) (fun i => V (i, j.2) ∘ A i) j.1
    (∀ side, MemW12 B (U side) (DU side)) →
    (∀ side, ∀ᵐ x ∂volume.restrict B.val, U side x ∈ N) →
    (∀ j, MemW12 B (V j) (DV j)) →
    (∀ j, ∀ᵐ x ∂volume.restrict B.val, (infDist (V j x) N) ^ 2 ≤ C j) →
    (∀ (side : Bool) (z : Domain 3), E (cubicalSignedFaceIsometry 3 (3 : Fin 4) side
      (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = U side z) →
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
        =ᵐ[volume.restrict S] (fun x => E (facet j (cubicalSignedFaceIsometry 2 i positive
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))))) →
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
  classical
  intro b e S B Ω A facet F hU hTarget hV hDist hTime KH hKH hKHEnd KV hKV hKVEnd
  let g := fun j : Fin 3 × Bool => E ∘ facet j
  have hData := fun j : Fin 3 × Bool => exists_cubical_signed_reordered_pair_and_traces
    (V j) (g j) (DV j) (Equiv.swap (Fin.last 2) j.1) (fun _ => true)
      (hV j) (KV j) (hKV j) (hKVEnd j)
  let DR := fun (j : Fin 3 × Bool) (y : Domain 3) (i : Fin 3) =>
    ∑ k : Fin 3, (A j.1 (EuclideanSpace.single i 1)) k • DV j (A j.1 y) k
  choose KR hKR hKREnd using fun j : Fin 3 × Bool => (hData j).2.2.1
  have hA (i : Fin 3) : A i = cubicalSignedFaceIsometry 2 i true := by
    rw [cubicalSignedFaceIsometry_as_signedPermutation]
    apply congrArg (cubicalSignedPermutation 3 (Equiv.swap (Fin.last 2) i))
    funext k
    simp only [ite_self]
  have hInv (i : Fin 3) (z : Domain 3) : A i (A i z) = z := by
    rw [hA]
    exact cubical_positive_face_isometry_involutive i z
  let DF : (Fin 4 × Bool) → Domain 3 → Gradient 3 q := fun j => Fin.lastCases (DU j.2) (fun i => DR (i, j.2)) j.1
  let K : (Fin 4 × Bool) → Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)) := fun j => Fin.lastCases (KH j.2) (fun i => KR (i, j.2)) j.1
  have hFace (j : Fin 4 × Bool) : MemW12 B (F j) (DF j) := by
    rcases j with ⟨j, side⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hU side
    · simpa only [F, DF, Fin.lastCases_castSucc] using (hData (i, side)).1
  obtain ⟨M₀, hM₀⟩ := hN.isBounded.exists_norm_le
  obtain ⟨M₁, hM₁⟩ := exists_uniform_norm_bound_of_compact_distance (volume.restrict B.val) V hN
    (target_nonempty_of_ae_unit_cube (U false) (hTarget false)) C hDist
  let M := max M₀ M₁
  have hBound (j : Fin 4 × Bool) : ∀ᵐ z ∂volume.restrict B.val, ‖F j z‖ ≤ M := by
    rcases j with ⟨j, side⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact (hTarget side).mono fun _ hz => (hM₀ _ hz).trans (le_max_left _ _)
    · simpa only [F, Fin.lastCases_castSucc] using
        (hData (i, side)).2.2.2 (fun z => ‖z‖ ≤ M)
          ((hM₁ (i, side)).mono fun _ hz => hz.trans (le_max_right _ _))
  have hRaw (j : Fin 4 × Bool) (i : Fin 3) : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F j (cubicalSignedFaceIsometry 2 i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F j (cubicalSignedFaceIsometry 2 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
    rcases j with ⟨j, side⟩
    refine Fin.lastCases ?_ (fun a => ?_) j
    · exact hKH side i
    · simpa only [F, K, Fin.lastCases_castSucc] using hKR (a, side) i
  have hEnd (j : Fin 4 × Bool) (i : Fin 3) (positive : Bool) :
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 2 → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (cubicalSignedFaceIsometry 3 j.1 j.2 (e.symm
          (cubicalSignedFaceIsometry 2 i positive (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1)))) := by
    rcases j with ⟨j, side⟩
    refine Fin.lastCases ?_ (fun a => ?_) j
    · filter_upwards [hKHEnd side i positive] with x hx
      exact hx.trans (hTime side _).symm
    · filter_upwards [hKREnd (a, side) i positive] with x hx
      change _ = E (cubicalSignedFaceIsometry 3 a.castSucc side (e.symm (A a (A a _), _))) at hx
      rw [hInv] at hx
      simpa only [K, Fin.lastCases_castSucc] using hx
  obtain ⟨G, D, hCap, hW, _hExact, hEnergy, hTrace, hProp⟩ :=
    exists_cubical_face_family_extension (n := 1) F DF E hFace M hBound K hRaw hEnd
  have hSum : (∑ j : Fin 4 × Bool, ∫ z in B.val, hsNormSq (DF j z)) =
      (∑ side : Bool, ∫ z in B.val, hsNormSq (DU side z)) +
        ∑ j : Fin 3 × Bool, ∫ z in B.val, hsNormSq (DV j z) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    simp only [DF, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [add_comm]
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro side _hs
    exact (hData (i, side)).2.1
  have hP (P : Ambient q → Prop) (hPU : ∀ side, ∀ᵐ z ∂volume.restrict B.val, P (U side z))
      (hPV : ∀ j, ∀ᵐ z ∂volume.restrict B.val, P (V j z)) : ∀ᵐ z ∂volume.restrict Ω.val, P (G (‖WithLp.ofLp z‖⁻¹ • z)) := by
    apply hProp P
    intro ⟨j, side⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hPU side
    · simpa only [F, Fin.lastCases_castSucc] using (hData (i, side)).2.2.2 P (hPV (i, side))
  refine ⟨G, D, hCap, hW, ?_, ?_, hTrace, hP⟩
  · change (∫ z in Ω.val, hsNormSq (D z)) ≤ (((3 : ℝ) + 1) / ((3 : ℝ) - 1)) * _ at hEnergy
    norm_num only [show (((3 : ℝ) + 1) / ((3 : ℝ) - 1)) = 2 by norm_num] at hEnergy
    rwa [hSum] at hEnergy
  · apply hP (fun z => (infDist z N) ^ 2 ≤ ∑ j : Fin 3 × Bool, max (C j) 0)
    · intro side
      filter_upwards [hTarget side] with z hz
      rw [infDist_zero_of_mem hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact Finset.sum_nonneg fun _ _ => le_max_right _ _
    · intro j
      exact (hDist j).mono fun _ hz => hz.trans ((le_max_left _ _).trans
        (Finset.single_le_sum (fun k _ => le_max_right (C k) 0) (Finset.mem_univ j)))

end StratificationTheory
