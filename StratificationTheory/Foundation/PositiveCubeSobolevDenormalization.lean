module

public import StratificationTheory.Foundation.UnitCubeAffineCoordinates
public import StratificationTheory.Foundation.CubicalConeGeometry

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- The literal inverse unit-cube similarity maps the whole positive
physical cube exactly to the whole original unit cube. -/
theorem inverse_unit_cube_preimage_unit_cube (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    F ⁻¹' (⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1) =
      ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε := by
  intro a F
  ext y
  simp only [mem_preimage, mem_iInter]
  change (∀ j : Fin n, -1 < (F y) j ∧ (F y) j < 1) ↔
    ∀ j : Fin n, 0 < y j ∧ y j < ε
  apply forall_congr'
  intro j
  change (-1 < (ε / 2)⁻¹ * (y j - ε / 2) ∧ (ε / 2)⁻¹ * (y j - ε / 2) < 1) ↔ _
  rw [mul_comm ((ε / 2)⁻¹), ← div_eq_mul_inv,
    lt_div_iff₀ (half_pos hε), div_lt_iff₀ (half_pos hε)]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The inverse physical similarity has the exact restricted native
measure coefficient on the original positive cube. -/
theorem map_inverse_affine_unit_cube_volume (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    let B := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let S := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    Measure.map F (volume.restrict S) = ENNReal.ofReal ((ε / 2) ^ n) • volume.restrict B := by
  intro a F B S
  have hPre : F ⁻¹' B = S := inverse_unit_cube_preimage_unit_cube n hε
  have hEmb : MeasurableEmbedding F := by
    simpa only [zero_add] using affineBall_measurableEmbedding (0 : Domain n) a
      (inv_ne_zero (half_pos hε).ne')
  have hMap : Measure.map F volume = ENNReal.ofReal ((ε / 2) ^ n) • volume := by
    simpa only [zero_add, inv_pow, inv_inv] using
      affineBall_map_volume (0 : Domain n) a (inv_pos.mpr (half_pos hε))
  have hB : MeasurableSet B := MeasurableSet.iInter fun j =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj j).continuous.measurable
  rw [← hPre, ← hEmb.restrict_map, hMap, Measure.restrict_smul]

/-- A genuine unit-cube weak map gives the same physical map on the
positive cube with its actual inverse-similarity columns and precise native
energy scaling. Every original a.e. value property is retained. -/
theorem memW12_positive_cube_denormalization_energy {n q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (V : Domain n → Ambient q) (DV : Domain n → Gradient n q) :
    let B : OpenDomain n :=
      ⟨⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let S : OpenDomain n :=
      ⟨⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
        isOpen_iInter_of_finite (fun j : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    let W := V ∘ F
    let D : Domain n → Gradient n q := fun y j => (ε / 2)⁻¹ • DV (F y) j
    MemW12 B V DV → MemW12 S W D ∧
      (∫ y in S.val, hsNormSq (D y)) =
        (ε / 2) ^ ((n : ℤ) - 2) * ∫ x in B.val, hsNormSq (DV x) ∧
      (∀ x : Domain n, W (a + (ε / 2) • x) = V x ∧
        ∀ j, D (a + (ε / 2) • x) j = (ε / 2)⁻¹ • DV x j) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (V x)) →
        ∀ᵐ y ∂volume.restrict S.val, P (W y) := by
  intro B S a F W D hV
  have hhalf : 0 < ε / 2 := half_pos hε
  have hData := memW12_affine_preimage_energy (volume_unit_coordinate_face_ne_top n)
    hV (0 : Domain n) a (inv_pos.mpr hhalf)
  have hPre : F ⁻¹' B.val = S.val := inverse_unit_cube_preimage_unit_cube n hε
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
  refine ⟨hW, hEnergy, ?_, ?_⟩
  · intro x
    have hInverse : F (a + (ε / 2) • x) = x := by
      simp only [F, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hhalf.ne', one_smul]
    exact ⟨congrArg V hInverse, fun j => by change (ε / 2)⁻¹ • DV (F _) j = _; rw [hInverse]⟩
  · have hProp := hData.2.2.2.2
    simp only [zero_add] at hProp
    change ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (V x)) →
      ∀ᵐ y ∂volume.restrict (F ⁻¹' B.val), P (W y) at hProp
    rwa [hPre] at hProp

end StratificationTheory
