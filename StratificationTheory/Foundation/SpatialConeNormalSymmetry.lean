module

public import StratificationTheory.Foundation.SpatialConeNormalLinearChart

/-!
# Actual spatial two-cone symmetry with independent time

The original spatial coordinate swap fixes the lateral plane, reverses its
unit normal, and retains the independent time coordinate. The full normal
linear chart is uniquely determined by its actual slices.
-/

public section
open HarmonicMaps
namespace StratificationTheory

theorem spatial_cone_normal_linear_chart_unique {n : ℕ}
    (F G : Domain (n + 1 + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1 + 1))
    (hF : ∀ y η, F ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)).symm
      (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n)
    (hG : ∀ y η, G ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)).symm
      (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n) : F = G := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
  have hs (t : Domain 1) : EuclideanSpace.single (0 : Fin 1) (t 0) = t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply,ite_true]
  apply ContinuousLinearEquiv.ext
  funext x
  have hf := hF (e x).1 ((e x).2 0)
  have hg := hG (e x).1 ((e x).2 0)
  have hr : e.symm ((e x).1,EuclideanSpace.single (0 : Fin 1) ((e x).2 0)) = x := by
    rw [hs,e.symm_apply_apply]
  change F (e.symm ((e x).1,EuclideanSpace.single (0 : Fin 1) ((e x).2 0))) = _ at hf
  change G (e.symm ((e x).1,EuclideanSpace.single (0 : Fin 1) ((e x).2 0))) = _ at hg
  rw [hr] at hf hg
  exact hf.trans hg.symm

/-- A genuine spatial swap exchanges the two cones and reverses the actual
normal parameter, while its entire independent time coordinate is fixed. -/
theorem exists_spatial_cone_normal_swap (n : ℕ) :
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let A := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    ∃ S : Domain (n + 1 + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1 + 1),
      (∀ z, S z = eF.symm (A (eF z).1,(eF z).2)) ∧
      (∀ z, S (S z) = z) ∧
      (∀ z, (eF (S z)).2 = (eF z).2) ∧
      ∀ (y : Domain (n + 1 + 1)) (η : ℝ),
        S (spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n) =
        spatialConeParallelSlice n 0 y + (-η) • spatialConeNormalVector n := by
  intro eF A
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let S := (eF.trans (ContinuousLinearEquiv.prodCongr A.toContinuousLinearEquiv
    (ContinuousLinearEquiv.refl ℝ (Domain 1)))).trans eF.symm
  have hS (z : Domain (n + 1 + 1 + 1)) : S z = eF.symm (A (eF z).1,(eF z).2) := rfl
  have hSwap : ∀ z, e (A z) =
      (b.symm ((b (e z).1).1,EuclideanSpace.single (0 : Fin 1) ((e z).2 0)),
        EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0)) :=
    (cubical_adjacent_cone_swap_coordinates n).1
  have hAA : ∀ z, A (A z) = z := (cubical_adjacent_cone_swap_coordinates n).2.1
  let γ : Domain (n + 1) → Domain (n + 1 + 1) := fun z =>
    e.symm (b.symm ((b z).1,EuclideanSpace.single (0 : Fin 1) ((b z).2 0)),
      EuclideanSpace.single (0 : Fin 1) ((b z).2 0))
  let ν₀ : Domain (n + 1 + 1) :=
    e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
  have hγ (z : Domain (n + 1)) : A (γ z) = γ z := by
    apply e.injective
    rw [hSwap]
    simp only [γ,e.apply_symm_apply,b.apply_symm_apply,PiLp.single_apply,ite_true]
  have hAν : A ν₀ = -ν₀ := (cubical_adjacent_cone_swap_coordinates n).2.2.2.1
  have hΓraw (y : Domain (n + 1 + 1)) : spatialConeParallelSlice n 0 y =
      eF.symm (γ (e y).1,(e y).2) := by
    rw [spatialConeParallelSlice_eq]
    change eF.symm (e.symm
      (b.symm ((b (e y).1).1,EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0 - 0)),
        EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0)),(e y).2) = _
    simp only [sub_zero]
    rfl
  have hνraw : spatialConeNormalVector n = eF.symm (ν₀,0) := by
    rw [spatialConeNormalVector_eq]
  have hSΓ (y : Domain (n + 1 + 1)) :
      S (spatialConeParallelSlice n 0 y) = spatialConeParallelSlice n 0 y := by
    rw [hS,hΓraw,eF.apply_symm_apply,hγ]
  have hSν : S (spatialConeNormalVector n) = -spatialConeNormalVector n := by
    rw [hS,hνraw,eF.apply_symm_apply,hAν,← eF.symm.map_neg]
    congr 1
    exact (show (-ν₀,(0 : Domain 1)) = -(ν₀,(0 : Domain 1)) by simp)
  refine ⟨S,hS,?_,?_,?_⟩
  · intro z
    rw [hS,hS,eF.apply_symm_apply,hAA,eF.symm_apply_apply]
  · intro z
    rw [hS,eF.apply_symm_apply]
  · intro y η
    rw [map_add,map_smul,hSΓ,hSν,neg_smul,smul_neg]

end StratificationTheory
