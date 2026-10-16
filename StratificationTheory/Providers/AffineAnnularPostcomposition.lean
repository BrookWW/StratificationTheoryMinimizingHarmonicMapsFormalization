module

public import StratificationTheory.Frozen.SphereGradientCharacterization
public import StratificationTheory.Frozen.UnitCylinder
public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic


import StratificationTheory.Interpolation.AffineCylinderPostcompositionEnergy
import StratificationTheory.Interpolation.AnnularAveragedEnergy
import HarmonicMaps.SobolevRestriction

/-!
# Affine postcomposition on the actual annulus

A single radially coherent cylinder extension supplies the postcomposed weak
columns. Smooth radial averaging gives the same annular map for weak membership,
original interior values and the native-to-volume energy comparison.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff
namespace StratificationTheory.Providers.AffineAnnularPostcomposition

private theorem postcomposition_radial_collar_columns {n q k : ℕ} {δ a b : ℝ}
    (F : Ambient q → Ambient k) (w : Domain (n + 1) → Ambient q)
    (D : Domain (n + 1) → Gradient (n + 1) q)
    (g : sphere (0 : Domain n) 1 × ℝ → Ambient q)
    (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
    (B : sphere (0 : Domain n) 1 × ℝ → Ambient q)
    (hraw : ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) = g (θ, t))
    (hD : ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t ∈ Ioo a b,
        let y := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
        (∀ i : Fin n, D y (Fin.castAdd 1 i) = ρ.val⁻¹ • A (θ, t) i) ∧
          D y (Fin.natAdd n (0 : Fin 1)) = B (θ, t)) :
    ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t ∈ Ioo a b,
        let y := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
        (∀ i : Fin n, fderiv ℝ F (w y) (D y (Fin.castAdd 1 i)) =
          ρ.val⁻¹ • fderiv ℝ F (g (θ, t)) (A (θ, t) i)) ∧
          fderiv ℝ F (w y) (D y (Fin.natAdd n (0 : Fin 1))) =
            fderiv ℝ F (g (θ, t)) (B (θ, t)) := by
  intro ρ hρ
  filter_upwards [hD ρ hρ] with θ hθ
  intro t ht
  dsimp only at hθ ⊢
  rw [hraw ρ hρ θ t ht]
  refine ⟨?_, ?_⟩
  · intro i
    rw [(hθ t ht).1 i, map_smul]
  · rw [(hθ t ht).2]


private theorem annular_average_raw_value {n q : ℕ} {s a b δ : ℝ}
    (hs : 0 < s) (ha : -1 < a) (P : Measure (Ioi (0 : ℝ))) (β : ℝ → ℝ)
    (w : Domain (n + 1) → Ambient q)
    (g : sphere (0 : Domain n) 1 × ℝ → Ambient q)
    (hP : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P, 1 - δ < ρ.val ∧ ρ.val < 1 + δ)
    (hmass : (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1)
    (hraw : ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) = g (θ, t)) :
    ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
      annularAveragedMap s β P w ((s * (1 + t)) • θ.val) = g (θ, t) := by
  intro θ t ht
  rw [annularAveragedMap_param hs (ha.trans ht.1) β P w θ]
  have hEq : (fun ρ : Ioi (0 : ℝ) => β ρ.val •
      w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t))) =ᵐ[P]
      (fun ρ => β ρ.val • g (θ, t)) := by
    filter_upwards [hP] with ρ hρ
    rw [hraw ⟨ρ.val, ρ.property⟩ hρ θ t ht]
  rw [integral_congr_ae hEq, integral_smul_const, hmass, one_smul]

theorem result {n q k : ℕ} (hn : 2 ≤ n)
    {a b s : ℝ} (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (C : NNReal) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    let V : OpenDomain n := ⟨{x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)},
      isOpen_Ioo.preimage continuous_norm⟩
    let κ := max (s * (1 + a))⁻¹ s⁻¹
    (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      ‖fderiv ℝ F (c y)‖ ≤ (C : ℝ)) →
    ∃ W : Domain n → Ambient k, ∃ DW : Domain n → Gradient n k,
      MemW12 V W DW ∧
      (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        W ((s * (1 + t)) • θ.val) =
          F ((1 - (t - a) / (b - a)) • u θ + ((t - a) / (b - a)) • v θ)) ∧
      (∫ x in V.val, hsNormSq (DW x)) ≤
        (s * (s * (1 + b)) ^ (n - 1)) * κ ^ 2 * (C : ℝ) ^ 2 *
          (((b - a) / 2) * (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
            (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
              ∂Measure.euclideanHausdorffMeasure (n - 1))) :=
by
  intro e c V κ hC
  obtain ⟨w, D, _hW, hraw, _hDunit, hAll, hFW, _hFraw, _hFc, hcols, _hInt, hEnergy⟩ :=
    exists_affine_cylinder_postcomposition_energy hn hab u v hu hv F hF L hDF C hC
  let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  let DPost : Domain (n + 1) → Gradient (n + 1) k :=
    fun x i => fderiv ℝ F (w x) (D x i)
  change MemW12 Ω (F ∘ w) DPost at hFW
  let δ : ℝ := 1 / 4
  have hδ : 0 < δ := by norm_num [δ]
  have hδsmall : δ < 1 / 2 := by norm_num [δ]
  let Γ : OpenDomain (n + 1) :=
    ⟨{y | (1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b},
      (((isOpen_lt continuous_const (continuous_fst.comp e.continuous).norm).inter
        (isOpen_lt (continuous_fst.comp e.continuous).norm continuous_const))).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
  have hΓsub : Γ.val ⊆ Ω.val := by
    intro y hy
    refine ⟨⟨?_, ?_⟩, hy.2⟩
    · have h := hy.1.1
      dsimp only [δ] at h
      linarith only [h]
    · have h := hy.1.2
      dsimp only [δ] at h
      linarith only [h]
  have hFWΓ : MemW12 Γ (F ∘ w) DPost :=
    ⟨hFW.1.mono hΓsub,
      hFW.2.1.mono_measure (Measure.restrict_mono_set volume hΓsub),
      fun i => (hFW.2.2 i).mono_measure (Measure.restrict_mono_set volume hΓsub)⟩
  let g : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p =>
    (1 - (p.2 - a) / (b - a)) • u p.1 + ((p.2 - a) / (b - a)) • v p.1
  let A₀ : sphere (0 : Domain n) 1 × ℝ → Gradient n q := fun p i =>
    (1 - (p.2 - a) / (b - a)) • (sphereGradient hn u hu i) p.1 +
      ((p.2 - a) / (b - a)) • (sphereGradient hn v hv i) p.1
  let B₀ : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p =>
    (b - a)⁻¹ • (v p.1 - u p.1)
  have hrawLocal : ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        w (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) = g (θ, t) := by
    intro ρ hρ θ t ht
    let y : unitCylinder n a b :=
      ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
        unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩
    have hsp : (e y.val).1 = θ.val := by simp only [y, e.apply_symm_apply]
    have htm : (e y.val).2 = EuclideanSpace.single (0 : Fin 1) t := by
      simp only [y, e.apply_symm_apply]
    have htime : (e y.val).2 0 ∈ Ioo a b := by
      simpa only [htm, PiLp.single_apply, ite_true] using ht
    have hradius : ρ.val • (e y.val).1 ∈ U.val := by
      rw [hsp]
      change 1 / 2 < ‖ρ.val • θ.val‖ ∧ ‖ρ.val • θ.val‖ < 2
      rw [norm_smul, Real.norm_of_nonneg ρ.property.le,
        mem_sphere_zero_iff_norm.mp θ.property, mul_one]
      dsimp only [δ] at hρ
      constructor <;> linarith only [hρ.1, hρ.2]
    have hy := hraw ρ y htime hradius
    change w (e.symm (ρ.val • (e y.val).1, (e y.val).2)) = c y at hy
    rw [hsp, htm] at hy
    convert hy using 1
    simp only [c, g, hsp, htm, PiLp.single_apply, ite_true]
  have hDLocal : ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t ∈ Ioo a b,
        let y := e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
        (∀ i : Fin n, D y (Fin.castAdd 1 i) = ρ.val⁻¹ • A₀ (θ, t) i) ∧
          D y (Fin.natAdd n (0 : Fin 1)) = B₀ (θ, t) := by
    intro ρ _hρ
    filter_upwards [hAll ρ] with θ hθ
    intro t _ht
    refine ⟨?_, ?_⟩
    · intro i
      have hi := congrFun (hθ t) (Fin.castAdd 1 i)
      simp only [Fin.addCases_left] at hi
      rw [hi]
      dsimp only [A₀]
      rw [smul_comm (1 - (t - a) / (b - a)) (ρ.val⁻¹),
        smul_comm ((t - a) / (b - a)) (ρ.val⁻¹), ← smul_add]
    · simpa only [B₀, Fin.addCases_right] using congrFun (hθ t) (Fin.natAdd n (0 : Fin 1))
  let A : sphere (0 : Domain n) 1 × ℝ → Gradient n k :=
    fun p i => fderiv ℝ F (g p) (A₀ p i)
  let B : sphere (0 : Domain n) 1 × ℝ → Ambient k :=
    fun p => fderiv ℝ F (g p) (B₀ p)
  have hPostCoherent := postcomposition_radial_collar_columns F w D g A₀ B₀ hrawLocal hDLocal
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
  let P := (η univ)⁻¹ • η
  obtain ⟨hP, β, hβ, hcβ, hsβ, _hβnonneg, hβmass⟩ :=
    exists_normalized_smooth_radial_weight (n := n) hδ
  let W := annularAveragedMap s β P (F ∘ w)
  let DW := annularAveragedColumns s β P DPost
  have hAvgW : MemW12 V W DW :=
    memW12_annularAveragedMap hn hab ha hs hFWΓ hδ hδsmall rfl hβ hcβ hsβ
  have hAvgEnergy := annularAveragedColumns_energy_le_native_of_radial_coherence
    (by omega : 0 < n) hFWΓ hδ hδsmall hab hs ha rfl A B β hcols hβmass hPostCoherent
  have hAEρ : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P, 1 - δ < ρ.val ∧ ρ.val < 1 + δ :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem
      ((isOpen_Ioo.preimage continuous_subtype_val).measurableSet))
  have hFrawLocal : ∀ (ρ : PositiveRadius), (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        (F ∘ w) (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) = F (g (θ, t)) := by
    intro ρ hρ θ t ht
    exact congrArg F (hrawLocal ρ hρ θ t ht)
  have hAvgRaw := annular_average_raw_value hs ha P β (F ∘ w) (F ∘ g) hAEρ hβmass hFrawLocal
  refine ⟨W, DW, hAvgW, hAvgRaw, ?_⟩
  have hhi : 0 < s * (1 + b) := mul_pos hs (by linarith only [ha, hab])
  have hfactor : 0 ≤ (s * (s * (1 + b)) ^ (n - 1)) * κ ^ 2 :=
    mul_nonneg (mul_nonneg hs.le (pow_nonneg hhi.le _)) (sq_nonneg κ)
  exact hAvgEnergy.2.2.trans (by
    calc
      _ ≤ ((s * (s * (1 + b)) ^ (n - 1)) * κ ^ 2) *
          ((C : ℝ) ^ 2 * _) := mul_le_mul_of_nonneg_left hEnergy hfactor
      _ = _ := by ring)

end StratificationTheory.Providers.AffineAnnularPostcomposition
