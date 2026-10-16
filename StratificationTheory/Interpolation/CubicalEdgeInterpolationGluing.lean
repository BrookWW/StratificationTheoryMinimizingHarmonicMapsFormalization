module

public import StratificationTheory.Foundation.IntervalSobolevProductGluing
public import StratificationTheory.Foundation.IntervalSobolevProductSpatialTrace
public import StratificationTheory.Interpolation.CubicalEdgeInterpolationGraph

/-!
# Gluing adjacent affine edge cylinders

Matching endpoint values of the two original line representatives glue their
integral weak graphs. The resulting actual affine rectangle has a continuous
spatial L2 trace curve whose two restrictions share the same cut trace.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Two adjacent line pairs sharing their actual endpoint values produce one
finite native rectangular weak graph. Its two local affine formulas agree
through the cut, and both continuous L2 edge traces have the same cut class. -/
theorem adjacent_interval_pair_rectangle_gluing {q : ℕ}
    {a b c τ₀ τ₁ : ℝ} (hab : a < b) (hbc : b < c) (hτ : τ₀ < τ₁)
    {F₀ F₁ G₀ G₁ f₀ f₁ h₀ h₁ g₀ g₁ k₀ k₁ : ℝ → Ambient q}
    (hf₀ : MemLp f₀ 2 (volume.restrict (Ioo a b)))
    (hf₁ : MemLp f₁ 2 (volume.restrict (Ioo b c)))
    (hh₀ : MemLp h₀ 2 (volume.restrict (Ioo a b)))
    (hh₁ : MemLp h₁ 2 (volume.restrict (Ioo b c)))
    (hg₀ : MemLp g₀ 2 (volume.restrict (Ioo a b)))
    (hg₁ : MemLp g₁ 2 (volume.restrict (Ioo b c)))
    (hk₀ : MemLp k₀ 2 (volume.restrict (Ioo a b)))
    (hk₁ : MemLp k₁ 2 (volume.restrict (Ioo b c)))
    (hF₀ : F₀ =ᵐ[volume.restrict (Ioo a b)] f₀)
    (hF₁ : F₁ =ᵐ[volume.restrict (Ioo b c)] f₁)
    (hG₀ : G₀ =ᵐ[volume.restrict (Ioo a b)] h₀)
    (hG₁ : G₁ =ᵐ[volume.restrict (Ioo b c)] h₁)
    (hFinc₀ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F₀ t - F₀ s = ∫ y in s..t, g₀ y)
    (hFinc₁ : ∀ s ∈ Icc b c, ∀ t ∈ Icc b c, F₁ t - F₁ s = ∫ y in s..t, g₁ y)
    (hGinc₀ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, G₀ t - G₀ s = ∫ y in s..t, k₀ y)
    (hGinc₁ : ∀ s ∈ Icc b c, ∀ t ∈ Icc b c, G₁ t - G₁ s = ∫ y in s..t, k₁ y)
    (hFmatch : F₀ b = F₁ b) (hGmatch : G₀ b = G₁ b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let α : Domain 2 → ℝ := fun y => ((e y).2 0 - τ₀) / (τ₁ - τ₀)
    let F := (Iic b).piecewise F₀ F₁
    let G := (Iic b).piecewise G₀ G₁
    let g := (Iic b).piecewise g₀ g₁
    let k := (Iic b).piecewise k₀ k₁
    let Ω : OpenDomain 2 :=
      ⟨{y : Domain 2 | (e y).1 0 ∈ Ioo a c ∧ (e y).2 0 ∈ Ioo τ₀ τ₁},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_fst.comp e.continuous))).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
    let W : Domain 2 → Ambient q := fun y =>
      (1 - α y) • F ((e y).1 0) + α y • G ((e y).1 0)
    let DW : Domain 2 → Gradient 2 q := fun y =>
      Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - α y) • g ((e y).1 0) + α y • k ((e y).1 0))
        (fun _ : Fin 1 => (τ₁ - τ₀)⁻¹ • (G ((e y).1 0) - F ((e y).1 0)))
    let ν : Measure ℝ := volume.restrict (Ioo τ₀ τ₁)
    let row : ℝ → ℝ → Ambient q := fun s t =>
      W (e.symm (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) t))
    MemW12 Ω W DW ∧
    (∀ y : Domain 2, (e y).1 0 ∈ Icc a b →
      W y = (1 - α y) • F₀ ((e y).1 0) + α y • G₀ ((e y).1 0)) ∧
    (∀ y : Domain 2, (e y).1 0 ∈ Icc b c →
      W y = (1 - α y) • F₁ ((e y).1 0) + α y • G₁ ((e y).1 0)) ∧
    ∃ H : C(Icc a c, Lp (Ambient q) 2 ν),
      ∃ L : C(Icc a b, Lp (Ambient q) 2 ν), ∃ R : C(Icc b c, Lp (Ambient q) 2 ν),
      (∀ s : Icc a c, ∃ hs : MemLp (row s.val) 2 ν, H s = hs.toLp (row s.val)) ∧
      (∀ s : Icc a b, L s = H ⟨s.val, s.property.1, s.property.2.trans hbc.le⟩) ∧
      (∀ s : Icc b c, R s = H ⟨s.val, hab.le.trans s.property.1, s.property.2⟩) ∧
      ∃ hcut : MemLp
        (fun t => (1 - (t - τ₀) / (τ₁ - τ₀)) • F₀ b + ((t - τ₀) / (τ₁ - τ₀)) • G₀ b) 2 ν,
      H ⟨b, hab.le, hbc.le⟩ = hcut.toLp
        (fun t => (1 - (t - τ₀) / (τ₁ - τ₀)) • F₀ b + ((t - τ₀) / (τ₁ - τ₀)) • G₀ b) ∧
      L ⟨b, hab.le, le_rfl⟩ = H ⟨b, hab.le, hbc.le⟩ ∧
      R ⟨b, le_rfl, hbc.le⟩ = H ⟨b, hab.le, hbc.le⟩ ∧
      (∀ K : C(Icc a b, Lp (Ambient q) 2 ν),
        (∀ᵐ s ∂volume, ∀ hs : s ∈ Ioo a b,
          ∃ hslice : MemLp (row s) 2 ν,
            K ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (row s)) → K = L) ∧
      ∀ K : C(Icc b c, Lp (Ambient q) 2 ν),
        (∀ᵐ s ∂volume, ∀ hs : s ∈ Ioo b c,
          ∃ hslice : MemLp (row s) 2 ν,
            K ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (row s)) → K = R := by
  intro e α F G g k Ω W DW ν row
  let f := (Iic b).piecewise f₀ f₁
  let h := (Iic b).piecewise h₀ h₁
  have hf : MemLp f 2 (volume.restrict (Ioo a c)) :=
    memLp_piecewise_adjacent_intervals hab hbc hf₀ hf₁
  have hh : MemLp h 2 (volume.restrict (Ioo a c)) :=
    memLp_piecewise_adjacent_intervals hab hbc hh₀ hh₁
  have hg : MemLp g 2 (volume.restrict (Ioo a c)) :=
    memLp_piecewise_adjacent_intervals hab hbc hg₀ hg₁
  have hk : MemLp k 2 (volume.restrict (Ioo a c)) :=
    memLp_piecewise_adjacent_intervals hab hbc hk₀ hk₁
  have hFae : F =ᵐ[volume.restrict (Ioo a c)] f :=
    ae_eq_piecewise_adjacent_intervals hab hbc hF₀ hF₁
  have hGae : G =ᵐ[volume.restrict (Ioo a c)] h :=
    ae_eq_piecewise_adjacent_intervals hab hbc hG₀ hG₁
  have hFinc := interval_piecewise_integral_increments hab hbc hg₀ hg₁ hFmatch hFinc₀ hFinc₁
  have hGinc := interval_piecewise_integral_increments hab hbc hk₀ hk₁ hGmatch hGinc₀ hGinc₁
  have hgraph := interval_pair_memW12_rectangle (hab.trans hbc) hτ hf hh hg hk
    hFae hGae hFinc hGinc
  have hFcont := continuousOn_interval_of_integral_increments (hab.trans hbc).le hg hFinc
  have hGcont := continuousOn_interval_of_integral_increments (hab.trans hbc).le hk hGinc
  let CF : C(Icc a c, Ambient q) := ⟨fun s => F s, hFcont.restrict⟩
  let CG : C(Icc a c, Ambient q) := ⟨fun s => G s, hGcont.restrict⟩
  let A : ℝ → ℝ := fun t => (t - τ₀) / (τ₁ - τ₀)
  let B : ℝ → ℝ := fun t => 1 - A t
  have hAcont : Continuous A := (continuous_id.sub continuous_const).div_const (τ₁ - τ₀)
  have hAtop : MemLp A ∞ ν := by
    apply memLp_top_of_bound hAcont.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hlo : 0 ≤ A t := div_nonneg (sub_nonneg.mpr ht.1.le) (sub_pos.mpr hτ).le
    have hhi : A t ≤ 1 := (div_le_one (sub_pos.mpr hτ)).mpr (sub_le_sub_right ht.2.le τ₀)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  have hA : MemLp A 2 ν := hAtop.mono_exponent (by norm_num)
  have hB : MemLp B 2 ν := (memLp_const (1 : ℝ)).sub hA
  obtain ⟨H, hHraw⟩ := continuous_weighted_pair_lp_slices ν hA hB CF CG
  have hRows : ∀ s : Icc a c, ∃ hs : MemLp (row s.val) 2 ν, H s = hs.toLp (row s.val) := by
    intro s
    simpa only [row, W, α, e.apply_symm_apply, PiLp.single_apply, ite_true, CF, CG,
      ContinuousMap.coe_mk, A, B] using hHraw s
  let ιL : C(Icc a b, Icc a c) :=
    ⟨fun s => ⟨s.val, s.property.1, s.property.2.trans hbc.le⟩,
      continuous_subtype_val.subtype_mk _⟩
  let ιR : C(Icc b c, Icc a c) :=
    ⟨fun s => ⟨s.val, hab.le.trans s.property.1, s.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let L := H.comp ιL
  let R := H.comp ιR
  have hcutPackage : ∃ hcut : MemLp (fun t => B t • F₀ b + A t • G₀ b) 2 ν,
      H ⟨b, hab.le, hbc.le⟩ = hcut.toLp (fun t => B t • F₀ b + A t • G₀ b) := by
    simpa only [CF, CG, ContinuousMap.coe_mk, F, G,
      Set.piecewise_eq_of_mem (Iic b) F₀ F₁ (mem_Iic.mpr (le_refl b)),
      Set.piecewise_eq_of_mem (Iic b) G₀ G₁ (mem_Iic.mpr (le_refl b))] using
      hHraw ⟨b, hab.le, hbc.le⟩
  obtain ⟨hcut, hcutEq⟩ := hcutPackage
  refine ⟨hgraph, ?_, ?_, H, L, R, hRows, fun _ => rfl, fun _ => rfl,
    hcut, hcutEq, rfl, rfl, ?_, ?_⟩
  · intro y hy
    exact congrArg₂ (fun x z => (1 - α y) • x + α y • z)
      (Set.piecewise_eq_of_mem (Iic b) F₀ F₁ hy.2)
      (Set.piecewise_eq_of_mem (Iic b) G₀ G₁ hy.2)
  · intro y hy
    by_cases hle : (e y).1 0 ≤ b
    · have heq : (e y).1 0 = b := le_antisymm hle hy.1
      dsimp only [W, F, G]
      rw [heq, Set.piecewise_eq_of_mem (Iic b) F₀ F₁ (mem_Iic.mpr (le_refl b)),
        Set.piecewise_eq_of_mem (Iic b) G₀ G₁ (mem_Iic.mpr (le_refl b)), hFmatch, hGmatch]
    · exact congrArg₂ (fun x z => (1 - α y) • x + α y • z)
        (Set.piecewise_eq_of_notMem (Iic b) F₀ F₁ hle)
        (Set.piecewise_eq_of_notMem (Iic b) G₀ G₁ hle)
  · intro K hK
    apply continuous_lp_curves_eq_of_ae_interior_slices ν hab L K (f := fun p : ℝ × ℝ => row p.2 p.1)
    · exact Eventually.of_forall (fun s hs => hRows ⟨s, hs.1.le, hs.2.le.trans hbc.le⟩)
    · exact hK
  · intro K hK
    apply continuous_lp_curves_eq_of_ae_interior_slices ν hbc R K (f := fun p : ℝ × ℝ => row p.2 p.1)
    · exact Eventually.of_forall (fun s hs => hRows ⟨s, hab.le.trans hs.1.le, hs.2.le⟩)
    · exact hK

end StratificationTheory
