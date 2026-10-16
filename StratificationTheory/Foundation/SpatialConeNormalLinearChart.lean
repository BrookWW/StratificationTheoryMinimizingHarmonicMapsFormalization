module

public import StratificationTheory.Foundation.SpatialConeNormalMaps
public import StratificationTheory.Foundation.CubicalAdjacentConeSwap
public import StratificationTheory.Foundation.LinearEquivSobolevPullback

/-!
# Actual full linear normal chart with independent time

The unnormalized spatial lateral parameter and its unit normal form a genuine
continuous linear coordinate isomorphism. The independent time value is
retained. Native weak graphs can therefore use the actual determinant-based
linear pullback.
-/

public section
open HarmonicMaps MeasureTheory Set
namespace StratificationTheory

/-- A genuine full linear coordinate isomorphism realizes the actual spatial
normal slices and the unchanged independent time coordinate. -/
theorem exists_spatial_cone_normal_linear_chart (n : ℕ) :
    ∃ F : Domain (n + 1 + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1 + 1),
      ∀ (y : Domain (n + 1 + 1)) (η : ℝ),
        F ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)).symm
          (y,EuclideanSpace.single (0 : Fin 1) η)) =
            spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n := by
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
  let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
  have hd : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  let σ : Domain 1 ≃L[ℝ] Domain 1 :=
    (Units.mk0 (Real.sqrt 2) hd) • ContinuousLinearEquiv.refl ℝ (Domain 1)
  let H : Domain (n + 1) ≃L[ℝ] Domain (n + 1) :=
    (b.trans (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n)) σ)).trans b.symm
  let HH : Domain (n + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1) :=
    (e.trans (ContinuousLinearEquiv.prodCongr H (ContinuousLinearEquiv.refl ℝ (Domain 1)))).trans e.symm
  obtain ⟨Q,hQ,_⟩ := exists_unique_native_cone_normal_coordinates n
  have hQF : ∀ v, e (Q v) =
      (b.symm ((b (e v).1).1,EuclideanSpace.single (0 : Fin 1)
        (((b (e v).1).2 0 - (e v).2 0) / Real.sqrt 2)),
        EuclideanSpace.single (0 : Fin 1) (((b (e v).1).2 0 + (e v).2 0) / Real.sqrt 2)) := hQ.1
  clear hQ
  let Fsp := HH.trans Q.toContinuousLinearEquiv
  let FB := (eF.trans (ContinuousLinearEquiv.prodCongr Fsp
    (ContinuousLinearEquiv.refl ℝ (Domain 1)))).trans eF.symm
  let A := cubicalSignedFaceIsometry (n + 2) (Fin.last (n + 1)).castSucc true
  let F := A.toContinuousLinearEquiv.trans FB
  have hsingle (z : Domain 1) : EuclideanSpace.single (0 : Fin 1) (z 0) = z := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply,ite_true]
  have hH (z : Domain (n + 1)) : H z = b.symm ((b z).1,(Real.sqrt 2) • (b z).2) := rfl
  have hHH (v : Domain (n + 1 + 1)) : HH v = e.symm (H (e v).1,(e v).2) := rfl
  have hFB (v : Domain (n + 1 + 1)) (t : Domain 1) :
      FB (eF.symm (v,t)) = eF.symm (Fsp v,t) := by
    change eF.symm (Fsp (eF (eF.symm (v,t))).1,(eF (eF.symm (v,t))).2) = _
    rw [eF.apply_symm_apply]
  have hA (y : Domain (n + 1 + 1)) (η : ℝ) :
      A (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η)) =
        eF.symm (e.symm ((e y).1,EuclideanSpace.single (0 : Fin 1) η),(e y).2) := by
    apply eF.injective
    have hswap := (cubical_adjacent_cone_swap_coordinates (n + 1)).1
    change ∀ v, eF (A v) =
      (e.symm ((e (eF v).1).1,EuclideanSpace.single (0 : Fin 1) ((eF v).2 0)),
        EuclideanSpace.single (0 : Fin 1) ((e (eF v).1).2 0)) at hswap
    have h := hswap (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η))
    simpa only [eF.apply_symm_apply,PiLp.single_apply,ite_true,hsingle] using h
  let γ : Domain (n + 1) → Domain (n + 1 + 1) := fun z =>
    e.symm (b.symm ((b z).1,EuclideanSpace.single (0 : Fin 1) ((b z).2 0)),
      EuclideanSpace.single (0 : Fin 1) ((b z).2 0))
  let ν₀ := e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
    EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
  have hsp (z : Domain (n + 1)) (η : ℝ) :
      Fsp (e.symm (z,EuclideanSpace.single (0 : Fin 1) η)) = γ z + η • ν₀ := by
    apply e.injective
    change e (Q (HH (e.symm (z,EuclideanSpace.single (0 : Fin 1) η)))) = _
    rw [hQF,hHH,e.apply_symm_apply,e.apply_symm_apply,hH,b.apply_symm_apply]
    simp only [PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul]
    rw [e.map_add,e.map_smul]
    simp only [γ,ν₀,e.apply_symm_apply]
    apply Prod.ext
    · change b.symm ((b z).1,EuclideanSpace.single (0 : Fin 1)
        ((Real.sqrt 2 * (b z).2 0 - η) / Real.sqrt 2)) =
        b.symm ((b z).1,EuclideanSpace.single (0 : Fin 1) ((b z).2 0)) +
          η • b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹))
      rw [← b.symm.map_smul,← b.symm.map_add]
      apply congrArg b.symm
      apply Prod.ext
      · simp
      · ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [Prod.snd_add,Prod.smul_snd,PiLp.add_apply,PiLp.smul_apply,
          PiLp.single_apply,ite_true,smul_eq_mul]
        field_simp
        ring
    · change EuclideanSpace.single (0 : Fin 1)
        ((Real.sqrt 2 * (b z).2 0 + η) / Real.sqrt 2) =
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0) +
          η • EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul]
      field_simp
  refine ⟨F,?_⟩
  intro y η
  change FB (A (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η))) = _
  rw [hA,hFB,hsp,spatialConeParallelSlice_eq,spatialConeNormalVector_eq]
  simp only [sub_zero]
  change eF.symm (γ (e y).1 + η • ν₀,(e y).2) =
    eF.symm (γ (e y).1,(e y).2) + η • eF.symm (ν₀,0)
  rw [← eF.symm.map_smul,← eF.symm.map_add]
  apply congrArg eF.symm
  apply Prod.ext
  · rfl
  · change (e y).2 = (e y).2 + η • (0 : Domain 1)
    simp

end StratificationTheory
