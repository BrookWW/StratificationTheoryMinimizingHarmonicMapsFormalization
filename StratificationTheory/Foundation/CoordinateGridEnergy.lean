module

public import StratificationTheory.Foundation.TranslatedGridSampling
public import StratificationTheory.Foundation.CoordinateACLRepresentative
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Joint energy sampling on actual Euclidean coordinate grids

The spatial grid is a scaled integer lattice in transverse coordinates.
Its line integrals use actual Euclidean volume and the canonical linear
spatial-time split. Two finite densities share one quantitative selection.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

private theorem lintegral_comp_of_aemeasurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {h : α → β} (hh : MeasurePreserving h μ ν)
    {f : β → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ x, f (h x) ∂μ) = ∫⁻ y, f y ∂ν := by
  calc
    _ = ∫⁻ x, hf.mk f (h x) ∂μ :=
      lintegral_congr_ae (hh.quasiMeasurePreserving.ae hf.ae_eq_mk)
    _ = ∫⁻ y, hf.mk f y ∂ν := hh.lintegral_comp hf.measurable_mk
    _ = _ := (lintegral_congr_ae hf.ae_eq_mk).symm

/-- Two finite actual Euclidean densities share one transverse cubical grid
with exact inverse-cell-volume scaling and their own bounds with constant two. -/
theorem exists_coordinate_grid_translate_pair_energy {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f g : Domain (n + 1) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume)
    (hfFinite : (∫⁻ y, f y) ≠ ⊤) (hgFinite : (∫⁻ y, g y) ≠ ⊤)
    {P : Domain n → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let b := (Pi.basisFun ℝ (Fin n)).isUnitSMul (fun _ => hε.ne'.isUnit)
    ∃ offset : Fin n → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range b), P (WithLp.toLp 2 ((z : Fin n → ℝ) + offset))) ∧
      (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t : ℝ,
        f (e.symm (WithLp.toLp 2 ((z : Fin n → ℝ) + offset),
          EuclideanSpace.single (0 : Fin 1) t))) ≤
        2 * (ENNReal.ofReal (ε ^ n))⁻¹ * ∫⁻ y, f y ∧
      (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t : ℝ,
        g (e.symm (WithLp.toLp 2 ((z : Fin n → ℝ) + offset),
          EuclideanSpace.single (0 : Fin 1) t))) ≤
        2 * (ENNReal.ofReal (ε ^ n))⁻¹ * ∫⁻ y, g y := by
  intro e b
  let H : (Fin n → ℝ) × ℝ → Domain (n + 1) := fun p =>
    e.symm (WithLp.toLp 2 p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  have hbase := (PiLp.volume_preserving_toLp (Fin n)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have hHraw := (measurePreserving_cylinder_coordinates_inverse n).comp hbase
  have hH : MeasurePreserving H
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) volume := hHraw
  have hfp : AEMeasurable (f ∘ H)
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) :=
    hf.comp_quasiMeasurePreserving hH.quasiMeasurePreserving
  have hgp : AEMeasurable (g ∘ H)
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) :=
    hg.comp_quasiMeasurePreserving hH.quasiMeasurePreserving
  let F : (Fin n → ℝ) → ℝ≥0∞ := fun x => ∫⁻ t : ℝ, f (H (x, t))
  let G : (Fin n → ℝ) → ℝ≥0∞ := fun x => ∫⁻ t : ℝ, g (H (x, t))
  have hF : AEMeasurable F volume := hfp.lintegral_prod_right'
  have hG : AEMeasurable G volume := hgp.lintegral_prod_right'
  have hFI : (∫⁻ x, F x) = ∫⁻ y, f y :=
    (lintegral_prod (f ∘ H) hfp).symm.trans (lintegral_comp_of_aemeasurable hH hf)
  have hGI : (∫⁻ x, G x) = ∫⁻ y, g y :=
    (lintegral_prod (g ∘ H) hgp).symm.trans (lintegral_comp_of_aemeasurable hH hg)
  have hPpi : ∀ᵐ x : Fin n → ℝ ∂volume, P (WithLp.toLp 2 x) :=
    (PiLp.volume_preserving_toLp (Fin n)).quasiMeasurePreserving.ae hP
  have hres := exists_grid_translate_pair_tsum_le hε hF hG
    (hFI ▸ hfFinite) (hGI ▸ hgFinite) hPpi
  rw [hFI, hGI] at hres
  dsimp only [F, G, H] at hres
  exact hres

/-- Two actual Sobolev maps give one transverse grid with both the total
gradient-energy bound and the discrepancy bound. Every retained grid line
uses the same canonical absolutely continuous representatives and original
weak columns. Zero total energies and zero-dimensional targets are included. -/
theorem exists_coordinate_grid_sobolev_pair_energy {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u v : Domain (n + 1) → Ambient q}
    {Du Dv : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv)
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball z R)
    {ε : ℝ} (hε : 0 < ε) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c := fun (x : Domain n) (t : ℝ) => e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
    let U : Domain n × ℝ → Ambient q := fun p => u (c p.1 p.2)
    let V : Domain n × ℝ → Ambient q := fun p => v (c p.1 p.2)
    let Gu : Domain n × ℝ → Ambient q := fun p => Du (c p.1 p.2) (Fin.natAdd n (0 : Fin 1))
    let Gv : Domain n × ℝ → Ambient q := fun p => Dv (c p.1 p.2) (Fin.natAdd n (0 : Fin 1))
    let Wu := fiberACLRepresentative a b U Gu
    let Wv := fiberACLRepresentative a b V Gv
    let E := (ball z R).indicator
      (fun y => ENNReal.ofReal (hsNormSq (Du y) + hsNormSq (Dv y)))
    let Δ := (ball z R).indicator (fun y => ENNReal.ofReal (‖u y - v y‖ ^ 2))
    let basis := (Pi.basisFun ℝ (Fin n)).isUnitSMul (fun _ => hε.ne'.isUnit)
    ∃ offset : Fin n → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let x := WithLp.toLp 2 ((l : Fin n → ℝ) + offset)
        x ∈ S →
          AbsolutelyContinuousOnInterval (fun t => Wu (x, t)) a b ∧
          AbsolutelyContinuousOnInterval (fun t => Wv (x, t)) a b ∧
          (fun t => Wu (x, t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => u (c x t)) ∧
          (fun t => Wv (x, t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => v (c x t)) ∧
          ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
            (Wu (x, t) - Wu (x, s) = ∫ r in s..t, Gu (x, r)) ∧
            (Wv (x, t) - Wv (x, s) = ∫ r in s..t, Gv (x, r))) ∧
      (∑' l : Submodule.span ℤ (Set.range basis), ∫⁻ t : ℝ,
        E (c (WithLp.toLp 2 ((l : Fin n → ℝ) + offset)) t)) ≤
        2 * (ENNReal.ofReal (ε ^ n))⁻¹ *
          (dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R)) ∧
      (∑' l : Submodule.span ℤ (Set.range basis), ∫⁻ t : ℝ,
        Δ (c (WithLp.toLp 2 ((l : Fin n → ℝ) + offset)) t)) ≤
        2 * (ENNReal.ofReal (ε ^ n))⁻¹ *
          ∫⁻ y in ball z R, ENNReal.ofReal (‖u y - v y‖ ^ 2) := by
  intro e c U V Gu Gv Wu Wv E Δ basis
  have hEu : AEMeasurable (fun y => ENNReal.ofReal (hsNormSq (Du y)))
      (volume.restrict (ball z R)) := hu.integrable_hsNormSq.aemeasurable.ennreal_ofReal
  have hE : AEMeasurable E volume := by
    apply (aemeasurable_indicator_iff measurableSet_ball).mpr
    exact (hu.integrable_hsNormSq.add hv.integrable_hsNormSq).aemeasurable.ennreal_ofReal
  have hEI : (∫⁻ y, E y) =
      dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R) := by
    rw [lintegral_indicator measurableSet_ball]
    simp_rw [ENNReal.ofReal_add (hsNormSq_nonneg (Du _)) (hsNormSq_nonneg (Dv _))]
    exact lintegral_add_left' hEu _
  have hΔI := (hu.2.1.sub hv.2.1).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hΔ : AEMeasurable Δ volume :=
    (aemeasurable_indicator_iff measurableSet_ball).mpr hΔI.aemeasurable.ennreal_ofReal
  have hΔtotal : (∫⁻ y, Δ y) = ∫⁻ y in ball z R, ENNReal.ofReal (‖u y - v y‖ ^ 2) :=
    lintegral_indicator measurableSet_ball _
  have hΔfinite : (∫⁻ y, Δ y) ≠ ⊤ := by
    rw [hΔtotal]
    exact (lintegral_ofReal_ne_top_iff_integrable hΔI.aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _)).mpr hΔI
  obtain ⟨_hWum, hWuae, hWuline⟩ := coordinateACLRepresentative_of_memW12_ball hR hu hS hab hrect
  obtain ⟨_hWvm, hWvae, hWvline⟩ := coordinateACLRepresentative_of_memW12_ball hR hv hS hab hrect
  have hWuslices := Measure.ae_ae_of_ae_prod hWuae
  have hWvslices := Measure.ae_ae_of_ae_prod hWvae
  let P : Domain n → Prop := fun x => x ∈ S →
    AbsolutelyContinuousOnInterval (fun t => Wu (x, t)) a b ∧
    AbsolutelyContinuousOnInterval (fun t => Wv (x, t)) a b ∧
    (fun t => Wu (x, t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => u (c x t)) ∧
    (fun t => Wv (x, t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => v (c x t)) ∧
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (Wu (x, t) - Wu (x, s) = ∫ r in s..t, Gu (x, r)) ∧
      (Wv (x, t) - Wv (x, s) = ∫ r in s..t, Gv (x, r))
  have hP : ∀ᵐ x ∂volume, P x := by
    apply (ae_restrict_iff' hS).mp
    filter_upwards [hWuline, hWvline, hWuslices, hWvslices] with x huLine hvLine huSlice hvSlice
    exact ⟨huLine.1, hvLine.1, huSlice, hvSlice,
      fun s hs t ht => ⟨huLine.2 s hs t ht, hvLine.2 s hs t ht⟩⟩
  have hEfinite : (∫⁻ y, E y) ≠ ⊤ := by
    rw [hEI]
    exact ENNReal.add_ne_top.mpr ⟨hu.dirichletEnergy_ne_top, hv.dirichletEnergy_ne_top⟩
  have hresult := exists_coordinate_grid_translate_pair_energy hε hE hΔ hEfinite hΔfinite hP
  rw [hEI, hΔtotal] at hresult
  exact hresult

end StratificationTheory
