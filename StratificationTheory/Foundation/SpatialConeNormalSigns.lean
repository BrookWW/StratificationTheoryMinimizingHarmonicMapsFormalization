module

public import StratificationTheory.Foundation.SpatialConeNormalLinearChart

/-!
# Actual signs of spatial normal coordinates

The genuine normal coordinate has the sign of spatial height minus the
adjacent spatial coordinate. Independent time does not enter this identity.
-/

public section
open HarmonicMaps
namespace StratificationTheory

theorem spatial_cone_normal_coordinate_signs {n : ℕ}
    (F : Domain (n + 1 + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1 + 1))
    (hF : ∀ y η, F ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)).symm
      (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    ∀ z : Domain (n + 1 + 1 + 1),
      (e (eF z).1).2 0 - (b (e (eF z).1).1).2 0 =
        Real.sqrt 2 * (eF (F.symm z)).2 0 ∧
      ((eF (F.symm z)).2 0 < 0 ↔ (e (eF z).1).2 0 < (b (e (eF z).1).1).2 0) := by
  intro b e eF
  let P := (ContinuousLinearMap.fst ℝ (Domain (n + 1 + 1)) (Domain 1)).comp eF.toContinuousLinearMap
  let Y := (ContinuousLinearMap.fst ℝ (Domain (n + 1)) (Domain 1)).comp
    (e.toContinuousLinearMap.comp P)
  let H := (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ (Domain (n + 1)) (Domain 1)).comp (e.toContinuousLinearMap.comp P))
  let K := (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp (b.toContinuousLinearMap.comp Y))
  let L := H - K
  have hL (z : Domain (n + 1 + 1)) (t : Domain 1) :
      L (eF.symm (z,t)) = (e z).2 0 - (b (e z).1).2 0 := by
    change (e (eF (eF.symm (z,t))).1).2 0 - (b (e (eF (eF.symm (z,t))).1).1).2 0 = _
    rw [eF.apply_symm_apply]
  have hΓraw (y : Domain (n + 1 + 1)) : spatialConeParallelSlice n 0 y =
      eF.symm (e.symm
        (b.symm ((b (e y).1).1,EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0)),
          EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0)),(e y).2) := by
    rw [spatialConeParallelSlice_eq]
    simp only [sub_zero]
    rfl
  have hLΓ (y : Domain (n + 1 + 1)) : L (spatialConeParallelSlice n 0 y) = 0 := by
    rw [hΓraw,hL]
    simp only [e.apply_symm_apply,b.apply_symm_apply,PiLp.single_apply,ite_true,sub_self]
  let ν₀ := e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
    EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
  have hνraw : spatialConeNormalVector n = eF.symm (ν₀,0) := spatialConeNormalVector_eq n
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hLν : L (spatialConeNormalVector n) = Real.sqrt 2 := by
    rw [hνraw,hL]
    simp only [ν₀,e.apply_symm_apply,b.apply_symm_apply,PiLp.single_apply,ite_true]
    apply (mul_left_inj' hp.ne').mp
    field_simp
    nlinarith only [hSq]
  have hSlice (y : Domain (n + 1 + 1)) (η : ℝ) :
      L (F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η))) = Real.sqrt 2 * η := by
    have hFr : F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n := hF y η
    rw [hFr,L.map_add,L.map_smul,hLΓ,hLν,zero_add]
    exact mul_comm _ _
  intro z
  have hsingle (t : Domain 1) : EuclideanSpace.single (0 : Fin 1) (t 0) = t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply,ite_true]
  have heq : L z = Real.sqrt 2 * (eF (F.symm z)).2 0 := by
    have h := hSlice (eF (F.symm z)).1 ((eF (F.symm z)).2 0)
    rw [hsingle,eF.symm_apply_apply,F.apply_symm_apply] at h
    exact h
  change (e (eF z).1).2 0 - (b (e (eF z).1).1).2 0 = _ at heq
  refine ⟨heq,?_⟩
  constructor <;> intro ht <;> nlinarith only [heq,hp,ht]

end StratificationTheory
