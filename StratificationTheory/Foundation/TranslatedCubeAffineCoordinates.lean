module

public import StratificationTheory.Foundation.PositiveCubeSobolevDenormalization
public import StratificationTheory.Foundation.FiniteCoordinateBoxVolume

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- The literal inverse similarity identifies every translated physical
coordinate cube with the entire original open unit cube. -/
theorem inverse_translated_cube_preimage_unit_cube (n : ℕ) {ε : ℝ} (hε : 0 < ε) (lo : Domain n) :
    let a : Domain n := lo + WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    F ⁻¹' (⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1) =
      ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (lo j) (lo j + ε) := by
  intro a F
  ext y
  simp only [mem_preimage, mem_iInter]
  change (∀ j : Fin n, -1 < (F y) j ∧ (F y) j < 1) ↔
    ∀ j : Fin n, lo j < y j ∧ y j < lo j + ε
  apply forall_congr'
  intro j
  change (-1 < (ε / 2)⁻¹ * (y j - (lo j + ε / 2)) ∧
    (ε / 2)⁻¹ * (y j - (lo j + ε / 2)) < 1) ↔ _
  rw [mul_comm ((ε / 2)⁻¹), ← div_eq_mul_inv,
    lt_div_iff₀ (half_pos hε), div_lt_iff₀ (half_pos hε)]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The same original translated inverse similarity has the exact native
restricted pushforward measure, on the whole physical cube. -/
theorem map_inverse_translated_cube_volume (n : ℕ) {ε : ℝ} (hε : 0 < ε) (lo : Domain n) :
    let a : Domain n := lo + WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    let B := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let S := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (lo j) (lo j + ε)
    Measure.map F (volume.restrict S) = ENNReal.ofReal ((ε / 2) ^ n) • volume.restrict B := by
  intro a F B S
  have hPre : F ⁻¹' B = S := inverse_translated_cube_preimage_unit_cube n hε lo
  have hEmb : MeasurableEmbedding F := by
    simpa only [zero_add] using affineBall_measurableEmbedding (0 : Domain n) a (inv_ne_zero (half_pos hε).ne')
  have hMap : Measure.map F volume = ENNReal.ofReal ((ε / 2) ^ n) • volume := by
    simpa only [zero_add, inv_pow, inv_inv] using affineBall_map_volume (0 : Domain n) a (inv_pos.mpr (half_pos hε))
  rw [← hPre, ← hEmb.restrict_map, hMap, Measure.restrict_smul]

/-- A genuine original unit weak pair produces its actual translated
physical cube pair, with exact native energy and original value constraints. -/
theorem memW12_translated_cube_denormalization_energy {n q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (lo : Domain n) (V : Domain n → Ambient q) (DV : Domain n → Gradient n q) :
    let B : OpenDomain n :=
      ⟨⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin n => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let S : OpenDomain n :=
      ⟨⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (lo j) (lo j + ε),
        isOpen_iInter_of_finite (fun j : Fin n => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let a : Domain n := lo + WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    let W := V ∘ F
    let D : Domain n → Gradient n q := fun y j => (ε / 2)⁻¹ • DV (F y) j
    MemW12 B V DV → MemW12 S W D ∧
      (∫ y in S.val, hsNormSq (D y)) = (ε / 2) ^ ((n : ℤ) - 2) * ∫ x in B.val, hsNormSq (DV x) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (V x)) →
        ∀ᵐ y ∂volume.restrict S.val, P (W y) := by
  intro B S a F W D hV
  have hData := memW12_affine_preimage_energy (volume_unit_coordinate_face_ne_top n)
    hV (0 : Domain n) a (inv_pos.mpr (half_pos hε))
  have hPre : F ⁻¹' B.val = S.val := inverse_translated_cube_preimage_unit_cube n hε lo
  have hF : Continuous F := by
    change Continuous (fun y : Domain n => (ε / 2)⁻¹ • (y - a))
    exact (continuous_const : Continuous (fun _ : Domain n => (ε / 2)⁻¹)).smul
      ((continuous_id : Continuous (fun y : Domain n => y)).sub continuous_const)
  let T : OpenDomain n := ⟨F ⁻¹' B.val, B.property.preimage hF⟩
  have hT : T = S := Subtype.ext hPre
  have hW : MemW12 T W D := by simpa only [zero_add] using hData.1
  rw [hT] at hW
  have hScale : ((ε / 2)⁻¹) ^ (2 - (n : ℤ)) = (ε / 2) ^ ((n : ℤ) - 2) := by
    rw [inv_zpow, ← zpow_neg]
    congr 1
    ring
  have hEnergy : (∫ y in F ⁻¹' B.val, hsNormSq (D y)) =
      ((ε / 2)⁻¹) ^ (2 - (n : ℤ)) * ∫ x in B.val, hsNormSq (DV x) := by
    simpa only [zero_add] using hData.2.2.1
  rw [hPre, hScale] at hEnergy
  refine ⟨hW, hEnergy, ?_⟩
  have hProp := hData.2.2.2.2
  simp only [zero_add] at hProp
  change ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (V x)) →
    ∀ᵐ y ∂volume.restrict (F ⁻¹' B.val), P (W y) at hProp
  rwa [hPre] at hProp

end StratificationTheory
