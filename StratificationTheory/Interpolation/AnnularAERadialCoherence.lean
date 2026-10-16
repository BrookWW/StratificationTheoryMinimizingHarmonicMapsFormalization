module

public import StratificationTheory.Foundation.ProductAEEquality
public import StratificationTheory.Interpolation.AnnularCoherentColumns
public import StratificationTheory.Foundation.AnnularColumnComparison
import StratificationTheory.Foundation.CylinderRadialAverage

/-!
# Annular energy from almost-everywhere radial coherence

Actual ambient weak columns and native sphere-time L2 fields determine the
same radially averaged annular columns. The radial coherence is required only
almost everywhere in the radial and sphere-time product measures.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal
namespace StratificationTheory

theorem annularAveragedColumns_ae_of_ae_radial_coherence {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ a b s : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hs : 0 < s) (ha : -1 < a)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
    (B : sphere (0 : Domain n) 1 × ℝ → Ambient q) (β : ℝ → ℝ) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Ioo a b))
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ i : Fin n, MemLp (fun p => A p i) 2 μ) → MemLp B 2 μ →
    (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1 →
    (∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
      ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      (∀ i : Fin n,
        Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
            (Fin.castAdd 1 i) = ρ.val⁻¹ • A p i) ∧
      Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
          (Fin.natAdd n (0 : Fin 1)) = B p) →
    ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      annularAveragedColumns s β P Dw ((s * (1 + p.2)) • p.1.val) =
        fun i => (s * (1 + p.2))⁻¹ • tangentialColumns p.1 (A p) i +
          (s⁻¹ * p.1.val i) • B p := by
  intro σ μ η P e hA hB hmass hAll
  let Z := fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
    e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)
  have hraw (k : Fin (n + 1)) : MemLp (fun p => Dw (Z p) k) 2 (μ.prod P) := by
    have hcolumn := hw.2.2 k
    rw [hΩ] at hcolumn
    exact (memLp_two_native_radial_collar_average hn hδ hδsmall a b hcolumn).2.1
  have hprob : IsProbabilityMeasure P := by
    have hcolumn := hw.2.2 (0 : Fin (n + 1))
    rw [hΩ] at hcolumn
    exact (memLp_two_native_radial_collar_average hn hδ hδsmall a b hcolumn).1
  letI : IsProbabilityMeasure P := hprob
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ, p.2 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  have hρmeas : AEStronglyMeasurable
      (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) => p.2.val) (μ.prod P) :=
    (measurable_subtype_coe.comp measurable_snd).aestronglyMeasurable
  have hSp (i : Fin n) : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      ∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
        Dw (Z (p, ρ)) (Fin.castAdd 1 i) = ρ.val⁻¹ • A p i := by
    have hf := hρmeas.smul (hraw (Fin.castAdd 1 i)).1
    have hg : AEStronglyMeasurable
        (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) => A p.1 i) (μ.prod P) :=
      (hA i).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hfSwap := hf.comp_measurePreserving (Measure.measurePreserving_swap (μ := P) (ν := μ))
    have hgSwap := hg.comp_measurePreserving (Measure.measurePreserving_swap (μ := P) (ν := μ))
    have hrows : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
        ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
          ρ.val • Dw (Z (p, ρ)) (Fin.castAdd 1 i) = A p i := by
      filter_upwards [hAll] with ρ hρ
      filter_upwards [hρ] with p hp
      rw [hp.1 i, smul_smul,
        mul_inv_cancel₀ (show ρ.val ≠ 0 from ne_of_gt ρ.property), one_smul]
    have hswap := ae_ae_eq_swap_of_aestronglyMeasurable hfSwap hgSwap hrows
    filter_upwards [hswap] with p hp
    filter_upwards [hp] with ρ hρ
    change ρ.val • Dw (Z (p, ρ)) (Fin.castAdd 1 i) = A p i at hρ
    have hmul := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hρ
    simpa only [Function.comp_def, Prod.swap_prod_mk, Pi.smul_apply, smul_smul,
      inv_mul_cancel₀ (show ρ.val ≠ 0 from ne_of_gt ρ.property), one_smul] using hmul
  have hTm : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      ∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
        Dw (Z (p, ρ)) (Fin.natAdd n (0 : Fin 1)) = B p := by
    have hf := (hraw (Fin.natAdd n (0 : Fin 1))).1
    have hg : AEStronglyMeasurable
        (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) => B p.1) (μ.prod P) :=
      hB.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hfSwap := hf.comp_measurePreserving (Measure.measurePreserving_swap (μ := P) (ν := μ))
    have hgSwap := hg.comp_measurePreserving (Measure.measurePreserving_swap (μ := P) (ν := μ))
    apply ae_ae_eq_swap_of_aestronglyMeasurable hfSwap hgSwap
    filter_upwards [hAll] with ρ hρ
    filter_upwards [hρ] with p hp
    exact hp.2
  have hSpAll := ae_all_iff.mpr hSp
  filter_upwards [hSpAll, hTm, htime] with p hp hpt htimep
  apply annularAveragedColumns_param_of_coherent_columns hs (ha.trans htimep.1)
    β P Dw p.1 (A p) (B p) hmass
  have hpall := ae_all_iff.mpr hp
  filter_upwards [hpall, hpt] with ρ hρ hρt
  exact ⟨hρ, hρt⟩

theorem annularAveragedColumns_energy_le_of_ae_radial_coherence {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ a b s : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hs : 0 < s) (ha : -1 < a) (hab : a < b)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
    (B : sphere (0 : Domain n) 1 × ℝ → Ambient q) (β : ℝ → ℝ) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Ioo a b))
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ i : Fin n, MemLp (fun p => A p i) 2 μ) → MemLp B 2 μ →
    (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1 →
    (∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
      ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      (∀ i : Fin n,
        Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
            (Fin.castAdd 1 i) = ρ.val⁻¹ • A p i) ∧
      Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
          (Fin.natAdd n (0 : Fin 1)) = B p) →
    let V := {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}
    let C := max (s * (1 + a))⁻¹ s⁻¹
    (∀ i : Fin n, MemLp (fun x => annularAveragedColumns s β P Dw x i) 2 (volume.restrict V)) ∧
      Integrable (fun x => hsNormSq (annularAveragedColumns s β P Dw x)) (volume.restrict V) ∧
      (∫ x in V, hsNormSq (annularAveragedColumns s β P Dw x)) ≤
        (s * (s * (1 + b)) ^ (n - 1)) * C ^ 2 *
          ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ := by
  intro σ μ η P e hA hB hmass hAll V C
  have hFormula := annularAveragedColumns_ae_of_ae_radial_coherence
    hn hw hδ hδsmall hs ha hΩ A B β hA hB hmass hAll
  exact annular_column_energy_le_of_native_formula
    hn hs ha hab (annularAveragedColumns s β P Dw) A B hA hB hFormula

end StratificationTheory
