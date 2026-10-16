module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators

namespace StratificationTheory

/-- The actual square chart exchanges the two physical coordinates and
the two native factors, and is its own inverse. -/
theorem unit_square_coordinate_swap :
    let A := cubicalSignedFaceIsometry 1 (0 : Fin 2) true
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    (∀ y : Domain 2, A y 0 = y 1 ∧ A y 1 = y 0 ∧ A (A y) = y) ∧
    ∀ (x : Domain 1) (t : ℝ), A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
      e.symm (EuclideanSpace.single (0 : Fin 1) t, x) := by
  intro A e
  have h₀ (y : Domain 2) : A y 0 = y 1 := by
    change cubicalSignedFaceIsometry 1 (0 : Fin 2) true y 0 = y 1
    simpa only [Equiv.swap_apply_left, ite_true, ite_self,
      show Fin.last 1 = (1 : Fin 2) by decide] using
      cubicalSignedFaceIsometry_apply (0 : Fin 2) true y (Fin.last 1)
  have h₁ (y : Domain 2) : A y 1 = y 0 := by
    change cubicalSignedFaceIsometry 1 (0 : Fin 2) true y 1 = y 0
    simpa only [Equiv.swap_apply_right, ite_true, ite_self,
      show Fin.last 1 = (1 : Fin 2) by decide] using
      cubicalSignedFaceIsometry_apply (0 : Fin 2) true y (0 : Fin 2)
  have hBase (y : Domain 2) : (e y).1 0 = y 0 := by
    change y (Fin.castSucc (0 : Fin 1)) = y 0
    exact congrArg (fun i : Fin 2 => y i) (by decide)
  have hTime (y : Domain 2) : (e y).2 0 = y 1 := by
    change y (Fin.natAdd 1 (0 : Fin 1)) = y 1
    exact congrArg (fun i : Fin 2 => y i) (by decide)
  refine ⟨fun y => ⟨h₀ y, h₁ y, ?_⟩, ?_⟩
  · ext i
    fin_cases i
    · change A (A y) 0 = y 0
      rw [h₀, h₁]
    · change A (A y) 1 = y 1
      rw [h₁, h₀]
  · intro x t
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [hBase]
      change A _ 0 = t
      rw [h₀]
      rw [← hTime]
      rw [e.apply_symm_apply]
      rfl
    · ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [hTime]
      change A _ 1 = x 0
      rw [h₁]
      rw [← hBase]
      rw [e.apply_symm_apply]

/-- Exchanging the actual spatial and temporal coordinates preserves the
same square weak graph, exactly permutes its physical columns, and
preserves its native gradient energy and all original a.e. value data. -/
theorem memW12_unit_square_swap_energy {q : ℕ}
    (V : Domain 2 → Ambient q) (DV : Domain 2 → Gradient 2 q) :
    let A := cubicalSignedFaceIsometry 1 (0 : Fin 2) true
    let B : OpenDomain 2 :=
      ⟨⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let D : Domain 2 → Gradient 2 q := fun y i => if i = 0 then DV (A y) 1 else DV (A y) 0
    MemW12 B V DV → MemW12 B (V ∘ A) D ∧
      (∫ y in B.val, hsNormSq (D y)) = ∫ y in B.val, hsNormSq (DV y) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict B.val, P (V y)) →
        ∀ᵐ y ∂volume.restrict B.val, P ((V ∘ A) y) := by
  intro A B D hV
  have hCube (x : Domain 2) : x ∈ B.val ↔ ‖WithLp.ofLp x‖ < 1 := by
    rw [mem_unit_coordinate_face_iff, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.norm_eq_abs]
  have hPre : A ⁻¹' B.val = B.val := by
    ext y
    change A y ∈ B.val ↔ y ∈ B.val
    rw [hCube, hCube, cubicalSignedFaceIsometry_coordinate_norm]
  have hPull := memW12_isometric_preimage_energy (volume_unit_coordinate_face_ne_top 2) hV A
  let B' : OpenDomain 2 := ⟨A ⁻¹' B.val, B.property.preimage A.continuous⟩
  have hB' : B' = B := Subtype.ext hPre
  have hColumn : (fun y i => ∑ j : Fin 2, (A (EuclideanSpace.single i 1)) j • DV (A y) j) = D := by
    funext y i
    have h₀ (z : Domain 2) : A z 0 = z 1 := (unit_square_coordinate_swap.1 z).1
    have h₁ (z : Domain 2) : A z 1 = z 0 := (unit_square_coordinate_swap.1 z).2.1
    by_cases hi : i = 0
    · subst i
      rw [Fin.sum_univ_two, h₀, h₁]
      simp [D]
    · have hi' : i = 1 := by
        have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
        apply Fin.ext
        change i.val = 1
        omega
      subst i
      rw [Fin.sum_univ_two, h₀, h₁]
      simp [D]
  have hW : MemW12 B' (V ∘ A) D := by simpa only [hColumn] using hPull.1
  rw [hB'] at hW
  refine ⟨hW, ?_, ?_⟩
  · have hEnergy := hPull.2.2.1
    change (∫ x in A ⁻¹' B.val, hsNormSq ((fun y i => ∑ j : Fin 2, (A (EuclideanSpace.single i 1)) j • DV (A y) j) x)) = _ at hEnergy
    rwa [hPre, hColumn] at hEnergy
  · have hProp := hPull.2.2.2.2
    change ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict B.val, P (V y)) →
      ∀ᵐ y ∂volume.restrict (A ⁻¹' B.val), P ((V ∘ A) y) at hProp
    rwa [hPre] at hProp

end StratificationTheory
