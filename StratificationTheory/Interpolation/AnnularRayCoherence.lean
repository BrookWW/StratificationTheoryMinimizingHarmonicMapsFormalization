module

public import StratificationTheory.Foundation.ProductAEEquality
public import StratificationTheory.Interpolation.AnnularCoherentColumns
import StratificationTheory.Foundation.CylinderRadialAverage

/-!
# Native almost-everywhere formula for ray-coherent annular columns

Original full cylinder L2 data make the column fields jointly measurable in
sphere, time and radius. Radial coherence can therefore be transferred from
each fixed radius to almost every sphere-time point before taking the literal
annular average. The same original averaged field is retained throughout.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal
namespace StratificationTheory

theorem annularAveragedColumns_ae_of_radial_collar_coherence {n q : ℕ} (hn : 0 < n)
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
    (∀ ρ : PositiveRadius, (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ᵐ θ ∂σ, ∀ t ∈ Ioo a b,
      (∀ i : Fin n,
        Dw (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) (Fin.castAdd 1 i) =
          ρ.val⁻¹ • A (θ, t) i) ∧
      Dw (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1)) = B (θ, t)) →
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
  have hAEρ : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P, 1 - δ < ρ.val ∧ ρ.val < 1 + δ :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem
      ((isOpen_Ioo.preimage continuous_subtype_val).measurableSet))
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
      filter_upwards [hAEρ] with ρ hρ
      have hθ := (Measure.quasiMeasurePreserving_fst (μ := σ) (ν := volume.restrict (Ioo a b))).ae (hAll ⟨ρ.val, ρ.property⟩ hρ)
      filter_upwards [hθ, htime] with p hp ht
      rw [(hp p.2 ht).1 i, smul_smul,
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
    filter_upwards [hAEρ] with ρ hρ
    have hθ := (Measure.quasiMeasurePreserving_fst (μ := σ) (ν := volume.restrict (Ioo a b))).ae (hAll ⟨ρ.val, ρ.property⟩ hρ)
    filter_upwards [hθ, htime] with p hp ht
    exact (hp p.2 ht).2
  have hSpAll := ae_all_iff.mpr hSp
  filter_upwards [hSpAll, hTm, htime] with p hp hpt htimep
  apply annularAveragedColumns_param_of_coherent_columns hs (ha.trans htimep.1)
    β P Dw p.1 (A p) (B p) hmass
  have hpall := ae_all_iff.mpr hp
  filter_upwards [hpall, hpt] with ρ hρ hρt
  exact ⟨hρ, hρt⟩

end StratificationTheory
