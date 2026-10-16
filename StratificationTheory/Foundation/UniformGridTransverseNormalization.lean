module

public import StratificationTheory.Foundation.UniformGridCarriers
public import StratificationTheory.Foundation.TranslatedCubeAffineCoordinates

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal

namespace StratificationTheory

/-- Adjacent normal cells have exactly the same original transverse affine
origin, on the entire native base carrier. -/
theorem uniformGrid_transverse_origin_update {n N : ℕ} (ε : ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (k : Fin N) :
    (WithLp.toLp 2 (fun j : Fin n =>
      (((Function.update z i k) ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) * ε) : Domain n) =
      WithLp.toLp 2 (fun j : Fin n => ((z ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) * ε) := by
  classical
  ext j
  have hne : (Equiv.swap (Fin.last n) i) j.castSucc ≠ i := by
    intro heq
    have h := (Equiv.swap (Fin.last n) i).injective
      (heq.trans (Equiv.swap_apply_left (Fin.last n) i).symm)
    exact Fin.castSucc_ne_last j h
  change (((Function.update z i k) ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) * ε = _
  rw [Function.update_of_ne hne]

/-- The actual physical transverse inverse similarity has the exact native
pushforward measure on the complete original mesh face. -/
theorem map_uniformGrid_transverse_inverse_similarity {n N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) :
    let U := uniformGridTransverseCell n N ε i z
    let S := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let l : Domain n := WithLp.toLp 2 (fun j => ((z ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) * ε)
    let F : Domain n → Domain n := fun x => (ε / 2)⁻¹ • (x - (l + WithLp.toLp 2 (fun _ => ε / 2)))
    Measure.map F (volume.restrict U.val) = ENNReal.ofReal ((ε / 2) ^ n) • volume.restrict S := by
  intro U S l F
  have hU : U.val = ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (l j) (l j + ε) := by
    ext x
    rw [mem_uniformGridTransverseCell_iff]
    simp only [mem_iInter, mem_preimage]
    apply forall_congr'
    intro j
    have hHi : l j + ε = (((z ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) + 1) * ε := by
      change ((z ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) * ε + ε = _
      ring
    rw [hHi]
    rfl
  rw [hU]
  exact map_inverse_translated_cube_volume n hε l

/-- Any original native unit-face a.e. property transfers through the
actual physical transverse inverse similarity on the whole mesh face. -/
theorem ae_uniformGrid_transverse_inverse_property {n N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (P : Domain n → Prop) :
    let U := uniformGridTransverseCell n N ε i z
    let S := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let l : Domain n := WithLp.toLp 2 (fun j => ((z ((Equiv.swap (Fin.last n) i) j.castSucc)).val : ℝ) * ε)
    let F : Domain n → Domain n := fun x => (ε / 2)⁻¹ • (x - (l + WithLp.toLp 2 (fun _ => ε / 2)))
    (∀ᵐ x ∂volume.restrict S, P x) → ∀ᵐ x ∂volume.restrict U.val, P (F x) := by
  intro U S l F hP
  have hMap := map_uniformGrid_transverse_inverse_similarity hε i z
  have hF : Measurable F := by
    change Measurable (fun x : Domain n => (ε / 2)⁻¹ • (x - (l + WithLp.toLp 2 (fun _ => ε / 2))))
    fun_prop
  have hQ : Measure.QuasiMeasurePreserving F (volume.restrict U.val) (volume.restrict S) :=
    ⟨hF, Measure.absolutelyContinuous_of_le_smul (le_of_eq hMap)⟩
  exact hQ.ae hP

end StratificationTheory
