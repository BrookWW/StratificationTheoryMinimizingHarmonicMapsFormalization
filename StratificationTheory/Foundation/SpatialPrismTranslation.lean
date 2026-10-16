module

public import StratificationTheory.Foundation.AffineDomainSobolevPullback
public import StratificationTheory.Foundation.SurfaceL2TraceTransport
public import StratificationTheory.Foundation.FiniteCoordinateBoxVolume

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Spatial translation preserves the same weak prism map, its exact
energy, every almost-everywhere value property, and both original temporal
classes of its complete continuous native L2 curve. -/
theorem spatial_prism_translation_with_original_time_trace {m q : ℕ}
    (base : Domain m) (ρ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (w : Fin 2 → Domain m → Ambient q)
    (W : Domain (m + 1) → Ambient q) (D : Domain (m + 1) → Gradient (m + 1) q) :
    let U : OpenDomain m :=
      ⟨⋂ j : Fin m, (fun x : Domain m => base j + x j) ⁻¹' Ioo (-ρ) ρ,
        isOpen_iInter_of_finite (fun j : Fin m =>
          isOpen_Ioo.preimage (continuous_const.add (EuclideanSpace.proj j).continuous))⟩
    let U₀ : OpenDomain m :=
      ⟨⋂ j : Fin m, (EuclideanSpace.proj j) ⁻¹' Ioo (-ρ) ρ,
        isOpen_iInter_of_finite (fun j : Fin m => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)
    let Ω := fun A : OpenDomain m => (⟨{y | (e y).1 ∈ A.val ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
      (A.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩ : OpenDomain (m + 1))
    let lift := e.symm (base, (0 : Domain 1))
    let F := fun x : Domain (m + 1) => x - lift
    let W₀ := W ∘ F
    let D₀ := D ∘ F
    MemW12 (Ω U) W D →
    ∀ H : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val)),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x : Domain m => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∃ hw : MemLp (fun x : Domain m => w 0 (base + x)) 2 (volume.restrict U.val),
      H ⟨0, le_rfl, hε.le⟩ = hw.toLp (fun x => w 0 (base + x))) →
    (∃ hw : MemLp (fun x : Domain m => w 1 (base + x)) 2 (volume.restrict U.val),
      H ⟨ε, hε.le, le_rfl⟩ = hw.toLp (fun x => w 1 (base + x))) →
    MemW12 (Ω U₀) W₀ D₀ ∧
    (∫ x in (Ω U₀).val, hsNormSq (D₀ x)) = ∫ x in (Ω U).val, hsNormSq (D x) ∧
    (∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict (Ω U).val, P (W x)) →
      ∀ᵐ x ∂volume.restrict (Ω U₀).val, P (W₀ x)) ∧
    ∃ H₀ : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U₀.val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
        ∃ hs : MemLp (fun x : Domain m => W₀ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U₀.val),
          H₀ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W₀ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      (∃ hw : MemLp (w 0) 2 (volume.restrict U₀.val), H₀ ⟨0, le_rfl, hε.le⟩ = hw.toLp (w 0)) ∧
      (∃ hw : MemLp (w 1) 2 (volume.restrict U₀.val), H₀ ⟨ε, hε.le, le_rfl⟩ = hw.toLp (w 1)) := by
  classical
  intro U U₀ e Ω lift F W₀ D₀ hW H hRaw hEnd₀ hEnd₁
  have hSpace (x : Domain (m + 1)) : (e (F x)).1 = (e x).1 - base := by
    simp only [F, map_sub, lift, e.apply_symm_apply, Prod.fst_sub]
  have hTime (x : Domain (m + 1)) : (e (F x)).2 0 = (e x).2 0 := by
    simp only [F, map_sub, lift, e.apply_symm_apply, Prod.snd_sub, sub_zero]
  have hPre : F ⁻¹' (Ω U).val = (Ω U₀).val := by
    ext x
    change ((e (F x)).1 ∈ U.val ∧ (e (F x)).2 0 ∈ Ioo (0 : ℝ) ε) ↔ _
    rw [hSpace, hTime]
    apply and_congr_left
    intro _
    simp only [U, U₀, mem_iInter, mem_preimage, PiLp.sub_apply, add_sub_cancel]
    rfl
  have hFinTime (x : Domain (m + 1)) : (e x).2 0 = x (Fin.last m) := by
    change x (Fin.natAdd m (0 : Fin 1)) = x (Fin.last m)
    apply congrArg (fun j : Fin (m + 1) => x j)
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_zero, Fin.val_last, add_zero]
  have hBox : (Ω U).val = ⋂ i : Fin (m + 1), (EuclideanSpace.proj i) ⁻¹'
      Ioo ((Fin.snoc (fun j : Fin m => -ρ - base j) (0 : ℝ) : Fin (m + 1) → ℝ) i)
        ((Fin.snoc (fun j : Fin m => ρ - base j) ε : Fin (m + 1) → ℝ) i) := by
    ext x
    constructor
    · rintro ⟨hx, ht⟩
      rw [mem_iInter]
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last, mem_preimage, PiLp.proj_apply, hFinTime] using ht
      · simp only [Fin.snoc_castSucc, mem_preimage, PiLp.proj_apply]
        have hj := mem_iInter.mp hx j
        change -ρ < base j + x j.castSucc ∧ base j + x j.castSucc < ρ at hj
        change -ρ - base j < x j.castSucc ∧ x j.castSucc < ρ - base j
        constructor <;> linarith [hj.1, hj.2]
    · intro hx
      rw [mem_iInter] at hx
      have ht := hx (Fin.last m)
      simp only [Fin.snoc_last, mem_preimage, PiLp.proj_apply] at ht
      refine ⟨?_, ht⟩
      rw [mem_iInter]
      intro j
      have hj := hx j.castSucc
      simp only [Fin.snoc_castSucc, mem_preimage, PiLp.proj_apply] at hj
      change -ρ < base j + x j.castSucc ∧ base j + x j.castSucc < ρ
      constructor <;> linarith [hj.1, hj.2]
  have hFinite : (volume : Measure (Domain (m + 1))) (Ω U).val ≠ ⊤ := by
    rw [hBox]
    exact volume_finite_coordinate_box_ne_top _ _ _
  have hData := memW12_affine_preimage_energy hFinite hW (-lift) (0 : Domain (m + 1)) (r := 1) zero_lt_one
  have hGx (x : Domain (m + 1)) : -lift + (1 : ℝ) • (x - 0) = F x := by
    simp only [one_smul, sub_zero, F]
    abel
  have hGnorm (x : Domain (m + 1)) : -lift + (x - 0) = F x := by
    dsimp only [F]
    abel
  have hGraph : MemW12 (Ω U₀) W₀ D₀ := by
    have hh := hData.1
    simp only [hGnorm, one_smul] at hh
    convert hh using 1
    · apply Subtype.ext
      exact hPre.symm
    · rfl
  have hEnergy : (∫ x in (Ω U₀).val, hsNormSq (D₀ x)) = ∫ x in (Ω U).val, hsNormSq (D x) := by
    simpa only [hGx, hGnorm, hPre, D₀, one_smul, Function.comp_apply, one_zpow, one_mul] using hData.2.2.1
  have hProp : ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict (Ω U).val, P (W x)) →
      ∀ᵐ x ∂volume.restrict (Ω U₀).val, P (W₀ x) := by
    simpa only [hGx, hGnorm, hPre, W₀] using hData.2.2.2.2
  let FH : Domain m ≃ₜ Domain m := Homeomorph.addRight (-base)
  have hFH (x : Domain m) : FH x = x - base := by change x + -base = x - base; rw [sub_eq_add_neg]
  have hBaseCancel x : base + FH x = x := by rw [hFH]; abel
  have hPreSpace : FH ⁻¹' U.val = U₀.val := by
    ext x
    have hCoord j : base j + FH x j = x j := congrArg (fun y : Domain m => y j) (hBaseCancel x)
    simp only [mem_preimage, U, U₀, mem_iInter, hCoord, PiLp.proj_apply]
  have hMap : Measure.map FH (volume.restrict U₀.val) = volume.restrict U.val := by
    rw [← hPreSpace, ← FH.measurableEmbedding.restrict_map]
    have hVolume : Measure.map FH (volume : Measure (Domain m)) = volume := map_add_right_eq_self volume (-base)
    rw [hVolume]
  obtain ⟨H₀, _hAll, hPull, _hUnique⟩ := exists_continuous_L2_curve_homeomorph_pullback
    FH (c := 1) (by norm_num) (by rw [hMap, one_smul]) H
  have hPrism (x : Domain m) (t : ℝ) : F (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
      e.symm (FH x, EuclideanSpace.single (0 : Fin 1) t) := by
    apply e.injective
    apply Prod.ext
    · rw [hSpace, e.apply_symm_apply, e.apply_symm_apply]
      exact (hFH x).symm
    · ext j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rw [hTime, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨hGraph, hEnergy, hProp, H₀, ?_, ?_, ?_⟩
  · filter_upwards [hRaw] with t ht hti
    obtain ⟨hs, hClass⟩ := ht hti
    obtain ⟨hs', hClass'⟩ := hPull ⟨t, hti.1.le, hti.2.le⟩ _ hs hClass
    have hf : (fun x : Domain m => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) ∘ FH =
        (fun x : Domain m => W₀ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
      funext x
      exact congrArg W (hPrism x t).symm
    rw [← hf]
    exact ⟨hs', hClass'⟩
  · obtain ⟨hw, hEnd⟩ := hEnd₀
    have hf : (fun x : Domain m => w 0 (base + x)) ∘ FH = w 0 := by funext x; simp only [Function.comp_apply, hBaseCancel]
    rw [← hf]
    exact hPull ⟨0, le_rfl, hε.le⟩ _ hw hEnd
  · obtain ⟨hw, hEnd⟩ := hEnd₁
    have hf : (fun x : Domain m => w 1 (base + x)) ∘ FH = w 1 := by funext x; simp only [Function.comp_apply, hBaseCancel]
    rw [← hf]
    exact hPull ⟨ε, hε.le, le_rfl⟩ _ hw hEnd

end StratificationTheory
