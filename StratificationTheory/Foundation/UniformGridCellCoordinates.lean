module

public import StratificationTheory.Foundation.UniformGridCarriers
public import StratificationTheory.Foundation.UniformGridGeometry
public import StratificationTheory.Foundation.FiniteCoordinateBoxVolume

public section

open HarmonicMaps MeasureTheory Set

namespace StratificationTheory

/-- Every actual uniform open cell lies in the whole positive mesh box. -/
theorem uniformGridCell_subset_box {d N : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Fin d → Fin N) :
    (uniformGridCell d N ε z).val ⊆ (uniformGridBox d N ε).val := by
  intro x hx
  apply (mem_uniformGridBox_iff d N ε x).mpr
  have h := (mem_uniformGridCell_iff d N ε z x).mp hx
  intro i
  have hlow : 0 ≤ ((z i).val : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε.le
  have hcast : ((z i).val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (z i).isLt
  exact ⟨hlow.trans_lt (h i).1,
    (h i).2.trans_le (mul_le_mul_of_nonneg_right hcast hε.le)⟩

/-- The original physical cell is exactly the original rotated native
transverse rectangle. -/
theorem uniformGridCell_as_face_rectangle (n N : ℕ) (ε : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) :
    let Q := cubicalSignedFaceIsometry n i true
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U := uniformGridTransverseCell n N ε i z
    (uniformGridCell (n + 1) N ε z).val =
      Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧
        (e y).2 0 ∈ Ioo ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε)} := by
  intro Q e U
  ext y
  rw [mem_uniformGridCell_iff]
  exact coordinate_box_face_chart i (fun k => (z k).val * ε)
    (fun k => ((z k).val + (1 : ℝ)) * ε) y

/-- Changing only the normal cell index leaves its complete actual native
transverse face carrier unchanged. -/
theorem uniformGridTransverseCell_update_normal {n N : ℕ} (ε : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (k : Fin N) :
    uniformGridTransverseCell n N ε i (Function.update z i k) =
      uniformGridTransverseCell n N ε i z := by
  classical
  apply Subtype.ext
  ext x
  rw [mem_uniformGridTransverseCell_iff, mem_uniformGridTransverseCell_iff]
  apply forall_congr'
  intro j
  have hne : (Equiv.swap (Fin.last n) i) j.castSucc ≠ i := by
    intro heq
    have h := (Equiv.swap (Fin.last n) i).injective
      (heq.trans (Equiv.swap_apply_left (Fin.last n) i).symm)
    exact Fin.castSucc_ne_last j h
  rw [Function.update_of_ne hne]

/-- Every original transverse cell has finite native volume. -/
theorem volume_uniformGridTransverseCell_ne_top (n N : ℕ) (ε : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) :
    (volume : Measure (Domain n)) (uniformGridTransverseCell n N ε i z).val ≠ ⊤ :=
  volume_finite_coordinate_box_ne_top n _ _

/-- A genuine shared physical mesh-face point lies in the actual open
normal rectangle spanning the two neighboring cells. -/
theorem uniformGrid_shared_face_point {n N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (hzi : 0 < (z i).val)
    (x : Domain (n + 1)) (hxi : x i = ((z i).val : ℝ) * ε)
    (hx : ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) :
    let Q := cubicalSignedFaceIsometry n i true
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (e (Q.symm x)).1 ∈ (uniformGridTransverseCell n N ε i z).val ∧
      (e (Q.symm x)).2 0 ∈ Ioo ((((z i).val - 1 : ℕ) : ℝ) * ε)
        ((((z i).val : ℝ) + 1) * ε) := by
  intro Q e
  have hTime : (e (Q.symm x)).2 0 = x i := by
    change Q.symm x (Fin.last n) = x i
    simpa only [ite_true] using cubicalSignedFaceIsometry_symm_apply i true x (Fin.last n)
  refine ⟨(mem_uniformGridTransverseCell_iff n N ε i z _).mpr ?_, ?_⟩
  · intro k
    have hne : (Equiv.swap (Fin.last n) i) k.castSucc ≠ i := by
      intro heq
      have h := (Equiv.swap (Fin.last n) i).injective
        (heq.trans (Equiv.swap_apply_left (Fin.last n) i).symm)
      exact Fin.castSucc_ne_last k h
    change Q.symm x k.castSucc ∈ _
    rw [cubicalSignedFaceIsometry_symm_apply, if_neg (Fin.castSucc_ne_last k)]
    exact hx _ hne
  · rw [hTime, hxi]
    have hcast : (((z i).val - 1 : ℕ) : ℝ) + 1 = (z i).val := by
      exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ (z i).val)
    constructor <;> nlinarith

end StratificationTheory
