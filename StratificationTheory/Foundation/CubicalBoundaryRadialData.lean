module

public import StratificationTheory.Foundation.CubicalSignedFaceConePair
public import StratificationTheory.Foundation.FiniteDisjointSobolevData

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators

namespace StratificationTheory

/-- Full original Sobolev data on every signed face produce one actual
radial map, one global L2 column field, all open-cone weak graphs and exact
native energy. Sobolev gluing on the cone seams is a separate assertion. -/
theorem exists_cubical_boundary_radial_data {n q : ℕ} (hn : 2 ≤ n)
    (G : Domain (n + 1) → Ambient q)
    (Df : (Fin (n + 1) × Bool) → Domain n → Gradient n q) :
    let J := Fin (n + 1) × Bool
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let f : J → Domain n → Ambient q := fun p x =>
      G (cubicalSignedFaceIsometry n p.1 p.2 (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω := ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let C : J → OpenDomain (n + 1) := fun p =>
      ⟨{y | (if p.2 then y p.1 else -y p.1) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ j : Fin (n + 1), j ≠ p.1 → |y j| < (if p.2 then y p.1 else -y p.1)},
        isOpen_cubical_signed_cone p.1 p.2⟩
    let W : Domain (n + 1) → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    (∀ p : J, MemW12 B (f p) (Df p)) →
      ∃ D : Domain (n + 1) → Gradient (n + 1) q,
        MemLp W 2 (volume.restrict Ω) ∧
        (∀ j : Fin (n + 1), MemLp (fun y => D y j) 2 volume) ∧
        (∀ p : J, MemW12 (C p) W D) ∧
        (∫ y in Ω, hsNormSq (D y)) =
          ((n : ℝ) - 1)⁻¹ * ∑ p : J, ∫ x in B.val,
            hsNormSq (Df p x) + ‖∑ k : Fin n, x k • Df p x k‖ ^ 2 ∧
        (∫ y in Ω, hsNormSq (D y)) ≤
          (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∑ p : J, ∫ x in B.val, hsNormSq (Df p x) ∧
        ∀ P : Ambient q → Prop,
          (∀ p : J, ∀ᵐ x ∂volume.restrict B.val, P (f p x)) →
            ∀ᵐ y ∂volume.restrict Ω, P (W y) := by
  classical
  intro J e f B Ω C W hface
  have hEach (p : J) : ∃ A : Domain (n + 1) → Gradient (n + 1) q,
      MemW12 (C p) W A ∧
      (∫ y in (C p).val, hsNormSq (A y)) =
        ((n : ℝ) - 1)⁻¹ * ∫ x in B.val,
          hsNormSq (Df p x) + ‖∑ k : Fin n, x k • Df p x k‖ ^ 2 ∧
      (∫ y in (C p).val, hsNormSq (A y)) ≤
        (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Df p x) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (f p x)) →
        ∀ᵐ y ∂volume.restrict (C p).val, P (W y) :=
    exists_cubical_signed_face_cone_pair hn p.1 p.2 G (Df p) (hface p)
  choose A hA using hEach
  have hDisj : Pairwise fun p q : J => Disjoint (C p).val (C q).val :=
    pairwise_disjoint_cubical_signed_cones n
  have hSub (p : J) : (C p).val ⊆ Ω := cubical_signed_cone_subset_unit_cube p.1 p.2
  have hCover : ∀ᵐ y ∂volume.restrict Ω, ∃ p : J, y ∈ (C p).val :=
    ae_unit_cube_mem_cubical_signed_cone hn
  let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
    ∑ p : J, (C p).val.indicator (A p) y
  have hData := finite_disjoint_sobolev_data Ω C hDisj hSub hCover W A (fun p => (hA p).1)
  have hEnergy : (∫ y in Ω, hsNormSq (D y)) =
      ((n : ℝ) - 1)⁻¹ * ∑ p : J, ∫ x in B.val,
        hsNormSq (Df p x) + ‖∑ k : Fin n, x k • Df p x k‖ ^ 2 := by
    rw [hData.2.2.2]
    simp_rw [(hA _).2.1]
    rw [Finset.mul_sum]
  have hBound : (∫ y in Ω, hsNormSq (D y)) ≤
      (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∑ p : J, ∫ x in B.val, hsNormSq (Df p x) := by
    rw [hData.2.2.2, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => (hA p).2.2.1
  refine ⟨D, hData.1, hData.2.1, hData.2.2.1, hEnergy, hBound, ?_⟩
  intro P hP
  have hPglobal (p : J) : ∀ᵐ y : Domain (n + 1) ∂volume,
      y ∈ (C p).val → P (W y) :=
    (ae_restrict_iff' (C p).property.measurableSet).mp ((hA p).2.2.2 P (hP p))
  filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hPglobal), hCover] with y hy hmem
  obtain ⟨p, hp⟩ := hmem
  exact hy p hp

end StratificationTheory
