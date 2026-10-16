module

public import StratificationTheory.Compactness.AnnularTranslation
public import StratificationTheory.Compactness.RadialTraceDilation
public import StratificationTheory.Interpolation.ProjectedLuckhausAnnularConnector
public import StratificationTheory.Interpolation.RadialThreePieceComparison
public import StratificationTheory.Frozen.SphereTargetValues
public import HarmonicMaps.Analysis.AffineBallSobolev
public import StratificationTheory.Foundation.PositiveThinAnnularScale

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- The original sphere data and radial trace classes give a genuine
comparison by compressing the inner map and inserting the projected
Luckhaus connector. The constants are chosen before the comparison maps. -/
theorem exists_trace_comparison_radius {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (Ω : OpenDomain n) (c : Domain n) (r T η a b : ℝ),
        0 < r → r < T → 0 < η → η < 1 / 8 →
        a ≤ r / 2 → (r + T) / 2 ≤ b → closedBall c T ⊆ Ω.val →
        ∀ (u v : Domain n → Ambient q) (Du Dv : Domain n → Gradient n q),
        MemW12 (ballDomain c T) u Du → MemW12 (ballDomain c T) v Dv →
        TakesValuesIn N (ballDomain c T) u → TakesValuesIn N (ballDomain c T) v →
        IsLocallyEnergyMinimizing N Ω u Du →
        ∀ (huS : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)))
          (hvS : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val))),
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) →
        TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) →
        let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
        ∀ (H G : C(Icc a b, Lp (Ambient q) 2 σ)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + t • θ.val)) 2 σ,
            H ⟨t, ht.1.le, ht.2.le⟩ =
              hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + t • θ.val))) →
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => v (c + t • θ.val)) 2 σ,
            G ⟨t, ht.1.le, ht.2.le⟩ =
              hslice.toLp (fun θ : sphere (0 : Domain n) 1 => v (c + t • θ.val))) →
        ∀ (har : a ≤ r) (hrb : r ≤ b),
        H ⟨r, har, hrb⟩ = huS.1.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) →
        G ⟨r, har, hrb⟩ = hvS.1.toLp (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) →
        let A := ∫ θ : sphere (0 : Domain n) 1,
          ∑ i : Fin n,
            (‖(sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) hvS i) θ‖ ^ 2 +
              ‖(sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) huS i) θ‖ ^ 2) ∂σ
        let D := ∫ θ : sphere (0 : Domain n) 1, ‖u (c + r • θ.val) - v (c + r • θ.val)‖ ^ 2 ∂σ
        C * η ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt A * Real.sqrt D + C * η ^ (-(n : ℤ)) * D < ρ ^ 2 →
        (∫ x in ball c r, hsNormSq (Du x)) ≤
          (∫ x in ball c r, hsNormSq (Dv x)) + 8 * C * r ^ (n - 2) * (η * A + η⁻¹ * D) := by
  obtain ⟨ρ, C, hρ, hC, hop⟩ :=
    Interpolation.exists_projected_luckhaus_annulus_operator hn N
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro Ω c r T η a b hr hrT hη hηsmall harhalf hmidb hclosed
    u v Du Dv hu hv huN hvN hmin huS hvS huSN hvSN σ H G hH hG har hrb hHr hGr A D hsmall
  let lo := r / (1 + η)
  let τ := 1 + η
  have hτ : 0 < τ := by dsimp only [τ]; linarith only [hη]
  obtain ⟨hlo, _hhalf, hlor, hscale, _hJac⟩ :=
    positive_thin_annular_scale hn hr hη hηsmall
  have hInv : r / τ = lo := rfl
  obtain ⟨W, DW, K, hW, hWN, hE, hK, hKa, hKb, _hKN⟩ :=
    hop r η hr hη hηsmall (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val))
      (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) hvS huS hvSN huSN hsmall
  change MemW12 ⟨{x : Domain n | lo < ‖x‖ ∧ ‖x‖ < r}, _⟩ W DW at hW
  change C(Icc lo r, Lp (Ambient q) 2 σ) at K
  have hWtranslate := memW12_annular_translation hW c
  let w : Domain n → Ambient q := fun x => W (x - c)
  let Dw : Domain n → Gradient n q := fun x i => DW (x - c) i
  have hw : MemW12 ⟨{x : Domain n | lo < ‖x - c‖ ∧ ‖x - c‖ < r},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ w Dw := hWtranslate.1
  have hwN : ∀ᵐ x ∂volume.restrict {x : Domain n | lo < ‖x - c‖ ∧ ‖x - c‖ < r},
      w x ∈ N.carrierSet := hWtranslate.2.2 (fun z => z ∈ N.carrierSet) hWN
  have hwE : (∫ x in {x : Domain n | lo < ‖x - c‖ ∧ ‖x - c‖ < r}, hsNormSq (Dw x)) ≤
      8 * C * r ^ (n - 2) * (η * A + η⁻¹ * D) := hWtranslate.2.1.trans_le hE
  have hvball : MemW12 (ballDomain c r) v Dv :=
    hv.to_memW12Loc.memW12_ball (closedBall_subset_ball hrT)
  let v₀ : Domain n → Ambient q := fun x => v (c + τ • (x - c))
  let Dv₀ : Domain n → Gradient n q := fun x i => τ • Dv (c + τ • (x - c)) i
  have hv₀ : MemW12 (ballDomain c lo) v₀ Dv₀ := by
    simpa only [hInv] using hvball.affineBall_pullback c hτ
  have hvNball : TakesValuesIn N (ballDomain c r) v :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrT.le) hvN
  have hv₀N : TakesValuesIn N (ballDomain c lo) v₀ := by
    change ∀ᵐ x ∂volume.restrict (ball c lo), v (c + τ • (x - c)) ∈ N.carrierSet
    simpa only [hInv] using ae_affineBall c c hτ r hvNball
  obtain ⟨J, hJ, hJr⟩ :=
    exists_dilated_inner_radial_trace σ v c hr hτ hlo hscale harhalf hrb G hG
  have hJmatch : J ⟨lo, by linarith only [hlo], le_rfl⟩ =
      K ⟨lo, le_rfl, hlor.le⟩ := (hJr.trans hGr).trans hKa.symm
  have hι (t : Icc r ((r + T) / 2)) : t.val ∈ Icc a b :=
    ⟨har.trans t.property.1, t.property.2.trans hmidb⟩
  let ι : C(Icc r ((r + T) / 2), Icc a b) :=
    ⟨fun t => ⟨t.val, hι t⟩, continuous_subtype_val.subtype_mk hι⟩
  let L := H.comp ι
  have hL : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r ((r + T) / 2),
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + t • θ.val)) 2 σ,
        L ⟨t, ht.1.le, ht.2.le⟩ =
          hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + t • θ.val)) := by
    filter_upwards [hH] with t hHt ht
    exact hHt ⟨har.trans_lt ht.1, ht.2.trans_le hmidb⟩
  have hKtranslate : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo lo r,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + t • θ.val)) 2 σ,
        K ⟨t, ht.1.le, ht.2.le⟩ =
          hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + t • θ.val)) := by
    filter_upwards [hK] with t hKt ht
    simpa only [w, add_sub_cancel_left] using hKt ht
  have hKmatch : K ⟨r, hlor.le, le_rfl⟩ =
      L ⟨r, le_rfl, by linarith only [hrT]⟩ := hKb.trans hHr.symm
  have hcmp := Interpolation.radial_three_piece_minimizer_energy_comparison hn
    N Ω c hlo hlor hrT v₀ w u Dv₀ Dw Du hv₀ hw hu hv₀N hwN huN hmin hclosed
    J K L hJ hKtranslate hL hJmatch hKmatch
  have hFactor : ENNReal.ofReal (τ ^ ((2 : ℤ) - (n : ℤ))) ≤ 1 :=
    (ENNReal.ofReal_le_ofReal (positive_compression_energy_factor_le_one hn hη)).trans_eq
      (by norm_num)
  have hE₀ : dirichletEnergy Dv₀ (ball c lo) ≤ dirichletEnergy Dv (ball c r) := by
    have hEq := dirichletEnergy_affineBall c c hτ r Dv
    change dirichletEnergy Dv₀ (ball c (r / τ)) =
      ENNReal.ofReal (τ ^ ((2 : ℤ) - (n : ℤ))) * dirichletEnergy Dv (ball c r) at hEq
    rw [hInv] at hEq
    rw [hEq]
    simpa only [one_mul] using mul_le_mul_left hFactor (dirichletEnergy Dv (ball c r))
  have hE₀Real : (dirichletEnergy Dv₀ (ball c lo)).toReal ≤
      (dirichletEnergy Dv (ball c r)).toReal :=
    ENNReal.toReal_mono hvball.dirichletEnergy_ne_top hE₀
  have hI₀ : IntegrableOn (fun x => hsNormSq (Dv₀ x)) (ball c lo) := hv₀.integrable_hsNormSq
  have hIv : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c r) := hvball.integrable_hsNormSq
  rw [dirichletEnergy_toReal hI₀, dirichletEnergy_toReal hIv] at hE₀Real
  linarith only [hcmp, hwE, hE₀Real]

end StratificationTheory.Compactness
