module

public import StratificationTheory.Frozen.CubicalFaceConeExtensionV2
public import StratificationTheory.Foundation.AffineDomainSobolevPullback
public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.CubicalConeAEValues

/-!
# Native face cones at arbitrary centers and scales

The original unit-face weak pair gives one actual finite Sobolev cone at
every positive height. Its translated physical carrier, native energy and
value integral, original raw rays and original a.e. values are explicit.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- The same native unit-face cone pair scales to every positive physical
height and arbitrary center, with exact native value and HS integrals. -/
theorem scaled_unit_face_cone_extension {n q : ℕ} (hn : 2 ≤ n)
    (c : Domain (n + 1)) {r : ℝ} (hr : 0 < r)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w Dw) :
    let B : OpenDomain n :=
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let C : OpenDomain (n + 1) :=
      ⟨T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ i : Fin n, {y : Domain (n + 1) | |X y i| < T y},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_lt (((EuclideanSpace.proj i).continuous.comp
            (continuous_fst.comp e.continuous)).abs)
            ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous))))⟩
    let W : Domain (n + 1) → Ambient q := fun y => w (ξ y)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun i : Fin n => (T y)⁻¹ • Dw (ξ y) i)
        (fun _last : Fin 1 => -((T y)⁻¹ • (∑ i : Fin n, (ξ y) i • Dw (ξ y) i)))
    let A : Domain (n + 1) → Domain (n + 1) := fun y => (0 : Domain (n + 1)) + r⁻¹ • (y - c)
    let U : OpenDomain (n + 1) :=
      ⟨A ⁻¹' C.val, C.property.preimage (affineBall_contDiff (0 : Domain (n + 1)) c r⁻¹).continuous⟩
    let V : Domain (n + 1) → Ambient q := W ∘ A
    let DV : Domain (n + 1) → Gradient (n + 1) q := fun y i => r⁻¹ • D (A y) i
    MemW12 U V DV ∧
      (∀ y : Domain (n + 1), y ∈ U.val ↔
        (e (y - c)).2 0 ∈ Ioo (0 : ℝ) r ∧
          ∀ i : Fin n, |(e (y - c)).1 i| < (e (y - c)).2 0) ∧
      (∫ y in U.val, ‖V y‖ ^ 2) =
        (r ^ (n + 1) / ((n : ℝ) + 1)) * ∫ x in B.val, ‖w x‖ ^ 2 ∧
      (∫ y in U.val, hsNormSq (DV y)) =
        (r ^ (n - 1) / ((n : ℝ) - 1)) * ∫ x in B.val,
          hsNormSq (Dw x) + ‖∑ i : Fin n, x i • Dw x i‖ ^ 2 ∧
      (∫ y in U.val, hsNormSq (DV y)) ≤
        r ^ (n - 1) * (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Dw x) ∧
      dirichletEnergy DV U.val = ENNReal.ofReal (r ^ (n - 1)) * dirichletEnergy D C.val ∧
      (∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (w x)) →
        ∀ᵐ y ∂volume.restrict U.val, P (V y)) ∧
      ∀ x ∈ B.val, ∀ t ∈ Ioc (0 : ℝ) 1,
        V (c + r • e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) = w x := by
  intro B e X T ξ C W D A U V DV
  obtain ⟨hW, _hξ, _hJac, _hWI, hvalue, _hDI, henergy, hbound, hraw, _htrace⟩ :=
    cubical_face_cone_extension_joint hn hw
  have hW' : MemW12 C W D := hW
  have hC : C.val = {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |(e y).1 i| < (e y).2 0} := by
    ext y
    simp only [C, X, T, mem_inter_iff, mem_preimage, mem_iInter, mem_setOf_eq]
  have hCfinite : (volume : Measure (Domain (n + 1))) C.val ≠ ⊤ := by
    rw [hC]
    exact volume_native_unit_face_cone_ne_top n
  have hscaled := memW12_affine_preimage_energy (n := n + 1) (q := q) (Ω := C)
    hCfinite hW' (0 : Domain (n + 1)) c (inv_pos.mpr hr)
  have hV : MemW12 U V DV := hscaled.1
  have hscale : (r⁻¹) ^ (2 - ((n + 1 : ℕ) : ℤ)) = r ^ (n - 1) := by
    have hexp : (2 : ℤ) - ((n + 1 : ℕ) : ℤ) = -((n - 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast, inv_pow, inv_inv]
  have hVvalue : (∫ y in U.val, ‖V y‖ ^ 2) =
      ((r⁻¹) ^ (n + 1))⁻¹ * ∫ y in C.val, ‖W y‖ ^ 2 := hscaled.2.1
  have hVenergy : (∫ y in U.val, hsNormSq (DV y)) =
      r ^ (n - 1) * ∫ y in C.val, hsNormSq (D y) := by
    simpa only [hscale] using hscaled.2.2.1
  refine ⟨hV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    change A y ∈ C.val ↔ _
    rw [hC]
    simp only [A, mem_setOf_eq, zero_add, map_smul]
    change ((0 < r⁻¹ * (e (y - c)).2 0 ∧ r⁻¹ * (e (y - c)).2 0 < 1) ∧
      ∀ i : Fin n, |r⁻¹ * (e (y - c)).1 i| < r⁻¹ * (e (y - c)).2 0) ↔ _
    have hhi (t : ℝ) : r⁻¹ * t < 1 ↔ t < r := by
      rw [mul_comm, ← div_eq_mul_inv, div_lt_one hr]
    simp only [abs_mul, abs_of_pos (inv_pos.mpr hr), mul_pos_iff_of_pos_left (inv_pos.mpr hr),
      mul_lt_mul_iff_right₀ (inv_pos.mpr hr), hhi, mem_Ioo]
  · rw [hVvalue, hvalue, inv_pow, inv_inv]
    ring
  · rw [hVenergy, henergy]
    ring
  · calc
      _ = _ := hVenergy
      _ ≤ r ^ (n - 1) * ((((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Dw x)) :=
        mul_le_mul_of_nonneg_left hbound (pow_nonneg hr.le _)
      _ = _ := by ring
  · simpa only [hscale] using hscaled.2.2.2.1
  · intro P hP
    have hPunit : ∀ᵐ y ∂volume.restrict C.val, P (W y) := by
      rw [hC]
      exact ae_native_unit_face_cone_pullback (n := n) (w := w) (P := P) hP
    exact hscaled.2.2.2.2 P hPunit
  · intro x hx t ht
    have hcancel (z : Domain (n + 1)) : A (c + r • z) = z := by
      simp only [A, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, zero_add]
    change W (A (c + r • e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t))) = w x
    rw [hcancel]
    exact hraw x hx t ht

end StratificationTheory
