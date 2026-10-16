module

public import StratificationTheory.Foundation.PositiveSpatialAnnularConePair
public import StratificationTheory.Foundation.IndependentTimeIsometry
public import StratificationTheory.Foundation.CubicalSignedFaceConeGeometry
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback

/-!
# Actual signed spatial annular cone pairs

Every original signed spatial face produces the same radial spatial-time
map on its true physical annular cone. A genuine spatial isometry retains
time, native energy and original value constraints.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StratificationTheory

theorem exists_signed_spatial_annular_cone_constant (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (q : ℕ) (ε : ℝ), ε ≤ 1 →
    ∀ (i : Fin (n + 1)) (positive : Bool)
      (G : Domain (n + 1) × ℝ → Ambient q)
      (Dw : Domain (n + 1) → Gradient (n + 1) q),
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let A := cubicalSignedFaceIsometry n i positive
    let S := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain n := ⟨S,isOpen_iInter_of_finite (fun k : Fin n =>
      isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨{z | (e z).1 ∈ S ∧ (e z).2 0 ∈ Ioo (0 : ℝ) ε},
        (B.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let w := fun z : Domain (n + 1) =>
      G (A (e.symm ((e z).1,EuclideanSpace.single (0 : Fin 1) 1)),(e z).2 0)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e (E y).1).2 0
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2)
    let D₀ : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y j =>
      ∑ k : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single j 1)) k • Dw (F y) k
    let V₀ : OpenDomain (n + 1 + 1) :=
      ⟨({y | T y ∈ Ioo (0 : ℝ) 1 ∧ ∀ k : Fin n, |(e (E y).1).1 k| < T y} ∩
        {y | ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1}) ∩ {y | (E y).2 0 ∈ Ioo (0 : ℝ) ε},
          isOpen_positive_spatial_annular_cone n ε⟩
    let W := fun y : Domain (n + 1 + 1) =>
      G (‖WithLp.ofLp (E y).1‖⁻¹ • (E y).1,(E y).2 0)
    MemW12 Ω w Dw →
    ∃ Q : Domain (n + 1 + 1) ≃ₗᵢ[ℝ] Domain (n + 1 + 1),
      (∀ y, Q y = E.symm (A (E y).1,(E y).2)) ∧
      (∀ y, Q.symm y = E.symm (A.symm (E y).1,(E y).2)) ∧
      let V : OpenDomain (n + 1 + 1) := ⟨Q.symm ⁻¹' V₀.val,V₀.property.preimage Q.symm.continuous⟩
      let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y j =>
        ∑ k : Fin (n + 1 + 1), (Q.symm (EuclideanSpace.single j 1)) k • D₀ (Q.symm y) k
      MemW12 V W D ∧
      (∀ y, y ∈ V.val ↔
        (((if positive then (E y).1 i else -(E y).1 i) ∈ Ioo (0 : ℝ) 1 ∧
          ∀ k : Fin (n + 1), k ≠ i → |(E y).1 k| < (if positive then (E y).1 i else -(E y).1 i)) ∧
          ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε) ∧
      (∫ y in V.val,hsNormSq (D y)) ≤ Cn * ∫ z in Ω.val,hsNormSq (Dw z) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ z ∂volume.restrict Ω.val,P (w z)) →
        ∀ᵐ y ∂volume.restrict V.val,P (W y) := by
  obtain ⟨Cn,hCn,hPositive⟩ := exists_positive_spatial_annular_cone_constant n
  refine ⟨Cn,hCn,?_⟩
  intro q ε hε i positive G Dw e E A S B Ω w T F D₀ V₀ W hw
  let Grot : Domain (n + 1) × ℝ → Ambient q := fun p => G (A p.1,p.2)
  let W₀ : Domain (n + 1 + 1) → Ambient q := fun y =>
    Grot (‖WithLp.ofLp (E y).1‖⁻¹ • (E y).1,(E y).2 0)
  have hPositiveData := hPositive q ε hε Grot Dw hw
  have hW₀ : MemW12 V₀ W₀ D₀ := hPositiveData.1
  obtain ⟨Q,hQ,hQinv,_hTime⟩ := exists_independent_time_isometry A
  have hQraw (y : Domain (n + 1 + 1)) : Q y = E.symm (A (E y).1,(E y).2) := hQ y
  have hQinvraw (y : Domain (n + 1 + 1)) : Q.symm y = E.symm (A.symm (E y).1,(E y).2) := hQinv y
  have hSubBall : V₀.val ⊆ ball (0 : Domain (n + 1 + 1)) 2 := by
    intro y hy
    apply mem_ball_zero_iff.mpr
    exact (spatial_cone_annular_transport_carrier hε y hy.1.1.1.1 hy.1.1.2 hy.1.2 hy.2).2.2.2
  have hFinite : (volume : Measure (Domain (n + 1 + 1))) V₀.val ≠ ⊤ :=
    ne_top_of_le_ne_top (isBounded_ball.measure_lt_top.ne) (measure_mono hSubBall)
  have hPull := memW12_isometric_preimage_energy hFinite hW₀ Q.symm
  refine ⟨Q,hQraw,hQinvraw,?_⟩
  intro V D
  have hMap : W₀ ∘ Q.symm = W := by
    funext y
    have hMaxInv : ‖WithLp.ofLp (A.symm (E y).1)‖ = ‖WithLp.ofLp (E y).1‖ := by
      have h := cubicalSignedFaceIsometry_coordinate_norm i positive (A.symm (E y).1)
      change ‖WithLp.ofLp (A (A.symm (E y).1))‖ = _ at h
      rw [A.apply_symm_apply] at h
      exact h.symm
    change G (A (‖WithLp.ofLp (E (Q.symm y)).1‖⁻¹ • (E (Q.symm y)).1),(E (Q.symm y)).2 0) = _
    rw [hQinvraw,E.apply_symm_apply,hMaxInv,A.map_smul,A.apply_symm_apply]
  have hW : MemW12 V W D := by
    have h := hPull.1
    change MemW12 V (W₀ ∘ Q.symm) D at h
    rwa [hMap] at h
  have hMem (y : Domain (n + 1 + 1)) : y ∈ V.val ↔
      (((if positive then (E y).1 i else -(E y).1 i) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), k ≠ i → |(E y).1 k| < (if positive then (E y).1 i else -(E y).1 i)) ∧
        ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E y).2 0 ∈ Ioo (0 : ℝ) ε := by
    change Q.symm y ∈ V₀.val ↔ _
    change (((e (E (Q.symm y)).1).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k : Fin n, |(e (E (Q.symm y)).1).1 k| < (e (E (Q.symm y)).1).2 0) ∧
      ‖(E (Q.symm y)).1‖ ∈ Ioo (1 / 4 : ℝ) 1) ∧ (E (Q.symm y)).2 0 ∈ Ioo (0 : ℝ) ε ↔ _
    rw [hQinvraw,E.apply_symm_apply,A.symm.norm_map]
    exact and_congr (and_congr (cubicalSignedFaceIsometry_strict_cone_iff i positive (E y).1) Iff.rfl) Iff.rfl
  refine ⟨hW,hMem,?_,?_⟩
  · exact hPull.2.2.1.trans_le hPositiveData.2.1
  · intro P hP
    have h := hPull.2.2.2.2 P (hPositiveData.2.2 P hP)
    change ∀ᵐ y ∂volume.restrict V.val,P ((W₀ ∘ Q.symm) y) at h
    rwa [hMap] at h

end StratificationTheory
