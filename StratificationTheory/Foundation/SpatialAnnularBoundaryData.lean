module

public import StratificationTheory.Foundation.SignedSpatialAnnularConePair
public import StratificationTheory.Foundation.SpatialAnnularConePartition
public import StratificationTheory.Foundation.FiniteDisjointSobolevData

/-!
# One actual spatial annular radial pair from all original faces

Original signed face-times-time graphs give one literal radial map and one
finite indicator-sum gradient. The actual native energy, L2 qualifications,
open-cone weak graphs and original values hold jointly. Cone seams remain
a separate weak gluing obligation.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

theorem exists_spatial_annular_boundary_data {n : ℕ} (hn : 2 ≤ n) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (q : ℕ) (ε : ℝ), ε ≤ 1 →
    ∀ (G : Domain (n + 1) × ℝ → Ambient q)
      (Df : (Fin (n + 1) × Bool) → Domain (n + 1) → Gradient (n + 1) q),
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let J := Fin (n + 1) × Bool
    let S := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let Ωf : OpenDomain (n + 1) :=
      ⟨{z | (e z).1 ∈ S ∧ (e z).2 0 ∈ Ioo (0 : ℝ) ε},
        ((isOpen_iInter_of_finite fun k : Fin n => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous).preimage
          (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let Ω : OpenDomain (n + 1 + 1) :=
      ⟨{y | ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1 ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε},
        isOpen_spatial_annular_slab n ε⟩
    let f := fun (j : J) (z : Domain (n + 1)) => G
      (cubicalSignedFaceIsometry n j.1 j.2 (e.symm ((e z).1,EuclideanSpace.single (0 : Fin 1) 1)),(e z).2 0)
    let C : J → OpenDomain (n + 1 + 1) := fun j =>
      ⟨{y | (((if j.2 then (E y).1 j.1 else -(E y).1 j.1) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), k ≠ j.1 → |(E y).1 k| < (if j.2 then (E y).1 j.1 else -(E y).1 j.1)) ∧
        ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε},
          isOpen_signed_spatial_annular_cone j.1 j.2 ε⟩
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e (E y).1).2 0
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2)
    let D₀ := fun (j : J) (y : Domain (n + 1 + 1)) (i : Fin (n + 1 + 1)) =>
      ∑ k : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) k • Df j (F y) k
    let W := fun y : Domain (n + 1 + 1) => G
      (‖WithLp.ofLp (E y).1‖⁻¹ • (E y).1,(E y).2 0)
    (∀ j : J, MemW12 Ωf (f j) (Df j)) →
    ∃ Q : J → (Domain (n + 1 + 1) ≃ₗᵢ[ℝ] Domain (n + 1 + 1)),
      (∀ j y, Q j y = E.symm (cubicalSignedFaceIsometry n j.1 j.2 (E y).1,(E y).2)) ∧
      (∀ j y, (Q j).symm y = E.symm ((cubicalSignedFaceIsometry n j.1 j.2).symm (E y).1,(E y).2)) ∧
      let A := fun (j : J) (y : Domain (n + 1 + 1)) (i : Fin (n + 1 + 1)) =>
        ∑ k : Fin (n + 1 + 1), ((Q j).symm (EuclideanSpace.single i 1)) k • D₀ j ((Q j).symm y) k
      let D := fun y : Domain (n + 1 + 1) => ∑ j : J,(C j).val.indicator (A j) y
      MemLp W 2 (volume.restrict Ω.val) ∧
      (∀ i : Fin (n + 1 + 1), MemLp (fun y => D y i) 2 volume) ∧
      (∀ j : J, MemW12 (C j) W D) ∧
      (∫ y in Ω.val,hsNormSq (D y)) ≤ Cn * ∑ j : J,∫ z in Ωf.val,hsNormSq (Df j z) ∧
      ∀ P : Ambient q → Prop, (∀ j : J, ∀ᵐ z ∂volume.restrict Ωf.val,P (f j z)) →
        ∀ᵐ y ∂volume.restrict Ω.val,P (W y) := by
  obtain ⟨Cn,hCn,hSigned⟩ := exists_signed_spatial_annular_cone_constant n
  refine ⟨Cn,hCn,?_⟩
  intro q ε hε G Df e E J S Ωf Ω f C T F D₀ W hFace
  have hEach (j : J) := hSigned q ε hε j.1 j.2 G (Df j) (hFace j)
  choose Q hQ hQinv hData using hEach
  refine ⟨Q,hQ,hQinv,?_⟩
  intro A D
  let V₀ : OpenDomain (n + 1 + 1) :=
    ⟨{y | ((T y ∈ Ioo (0 : ℝ) 1 ∧ ∀ k : Fin n, |(e (E y).1).1 k| < T y) ∧
      ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε},
        isOpen_positive_spatial_annular_cone n ε⟩
  have hCarrier (j : J) :
      (⟨(Q j).symm ⁻¹' V₀.val,V₀.property.preimage (Q j).symm.continuous⟩ :
          OpenDomain (n + 1 + 1)) = C j := by
    apply Subtype.ext
    exact Set.ext (hData j).2.1
  have hW (j : J) : MemW12 (C j) W (A j) := by
    have h := (hData j).1
    change MemW12 (⟨(Q j).symm ⁻¹' V₀.val,V₀.property.preimage (Q j).symm.continuous⟩ :
      OpenDomain (n + 1 + 1)) W (A j) at h
    rwa [hCarrier j] at h
  have hE (j : J) : (∫ y in (C j).val,hsNormSq (A j y)) ≤
      Cn * ∫ z in Ωf.val,hsNormSq (Df j z) := by
    have h := (hData j).2.2.1
    change (∫ y in (Q j).symm ⁻¹' V₀.val,hsNormSq (A j y)) ≤ _ at h
    have hc : (Q j).symm ⁻¹' V₀.val = (C j).val := congrArg Subtype.val (hCarrier j)
    rwa [hc] at h
  have hP (j : J) (P : Ambient q → Prop)
      (hPf : ∀ᵐ z ∂volume.restrict Ωf.val,P (f j z)) :
      ∀ᵐ y ∂volume.restrict (C j).val,P (W y) := by
    have h := (hData j).2.2.2 P hPf
    change ∀ᵐ y ∂volume.restrict ((Q j).symm ⁻¹' V₀.val),P (W y) at h
    have hc : (Q j).symm ⁻¹' V₀.val = (C j).val := congrArg Subtype.val (hCarrier j)
    rwa [hc] at h
  have hDisjoint : Pairwise fun j k : J => Disjoint (C j).val (C k).val :=
    pairwise_disjoint_spatial_annular_signed_cones n ε
  have hSub (j : J) : (C j).val ⊆ Ω.val := fun _ hy => ⟨hy.1.2,hy.2⟩
  have hCover : ∀ᵐ y ∂volume.restrict Ω.val,∃ j : J,y ∈ (C j).val :=
    ae_spatial_annular_mem_signed_cone hn ε
  have hFinite := finite_disjoint_sobolev_data Ω.val C hDisjoint hSub hCover W A hW
  refine ⟨hFinite.1,hFinite.2.1,hFinite.2.2.1,?_,?_⟩
  · rw [hFinite.2.2.2,Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hE j
  · intro P hPf
    have hPoint (j : J) : ∀ᵐ y : Domain (n + 1 + 1) ∂volume,
        y ∈ (C j).val → P (W y) := (ae_restrict_iff' (C j).property.measurableSet).mp (hP j P (hPf j))
    filter_upwards [hCover,ae_restrict_of_ae (ae_all_iff.mpr hPoint)] with y hy hpy
    obtain ⟨j,hj⟩ := hy
    exact hpy j hj

end StratificationTheory
