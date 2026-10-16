module

public import StratificationTheory.Foundation.CoherentNativeCylinderL2

/-!
# Native tangency from actual ambient radial annihilation

The native cylinder tangency identity is recovered from the same ambient
column family and its genuine almost-everywhere radius coherence. The proof
uses exact native polar measure and a positive-measure radius band.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- Actual ambient radial annihilation and the original coherence identify
the native spatial columns as a tangent family on the same cylinder. -/
theorem native_cylinder_tangency_of_real_radial_coherence {n q : ℕ}
    (hn : 0 < n) {ε R a b : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (DW : Domain (n + 1) → Gradient (n + 1) q)
    (g : unitCylinder n a b → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    (∀ᵐ y ∂volume.restrict {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b},
      ∑ i : Fin n, (e y).1 i • DW y (Fin.castAdd 1 i) = 0) →
    (∀ᵐ r ∂volume.restrict (Ioo ε R), ∀ᵐ c ∂μ, (e c.val).2 0 ∈ Ioo a b →
      ∀ i : Fin n, DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
        r⁻¹ • g c (Fin.castAdd 1 i)) →
    ∀ᵐ c ∂μ, ∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i) = 0 := by
  intro e μ hrad hcoh
  let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν
      (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  letI : SFinite μ := (unitCylinder_param_measurePreserving hn a b).2.sfinite
  have hprod := (measurePreserving_native_cylinder_radial_inverse hn hε R a b).quasiMeasurePreserving.ae hrad
  change ∀ᵐ p : unitCylinder n a b × Ioi (0 : ℝ) ∂μ.prod η,
    ∑ i : Fin n, (e (e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2))).1 i •
      DW (e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2)) (Fin.castAdd 1 i) = 0 at hprod
  have hrows : ∀ᵐ ρ ∂η, ∀ᵐ c ∂μ,
      ∑ i : Fin n, (ρ.val • (e c.val).1) i •
        DW (e.symm (ρ.val • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) = 0 := by
    have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod
    have h := Measure.ae_ae_of_ae_prod hswap
    simpa only [Function.comp_apply, Prod.swap_prod_mk, e.apply_symm_apply] using h
  have hcohη : ∀ᵐ ρ ∂η, ∀ᵐ c ∂μ, (e c.val).2 0 ∈ Ioo a b →
      ∀ i : Fin n, DW (e.symm (ρ.val • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
        ρ.val⁻¹ • g c (Fin.castAdd 1 i) :=
    (ae_positive_radius_band_iff (n := n) hε _).mpr hcoh
  have hconstant : ∀ᵐ ρ ∂η, ∀ᵐ c ∂μ,
      ∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i) = 0 := by
    filter_upwards [hrows, hcohη] with ρ hρ hρc
    filter_upwards [hρ, hρc, ae_unitCylinder_time_mem_Ioo hn a b] with c hc heq hct
    have hrzero : (ρ.val : ℝ) ≠ 0 := ne_of_gt ρ.property
    have hterm (i : Fin n) :
        (ρ.val • (e c.val).1) i •
          DW (e.symm (ρ.val • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
          (e c.val).1 i • g c (Fin.castAdd 1 i) := by
      rw [heq hct i, PiLp.smul_apply, smul_eq_mul, smul_smul]
      congr 1
      field_simp [hrzero]
    simpa only [hterm] using hc
  have hreal : ∀ᵐ _r ∂volume.restrict (Ioo ε R),
      ∀ᵐ c ∂μ, ∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i) = 0 :=
    (ae_positive_radius_band_iff (n := n) hε _).mp hconstant
  letI : NeZero ((volume : Measure ℝ).restrict (Ioo ε R)) := ⟨by
    intro hz
    have h := congrArg (fun m : Measure ℝ => m univ) hz
    have hzero : ENNReal.ofReal (R - ε) = 0 := by simpa using h
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hεR)).ne' hzero⟩
  obtain ⟨r, hr⟩ := hreal.exists
  exact hr

end StratificationTheory
