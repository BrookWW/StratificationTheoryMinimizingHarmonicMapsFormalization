module

public import StratificationTheory.Interpolation.RadialThreePieceGluing
public import StratificationTheory.Foundation.RadialPiecewiseProperties
public import HarmonicMaps.Minimizer

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory.Interpolation

/-- Original local minimality compares inner energy with an actual target
valued insertion and connecting annulus. The exterior energy cancels after
the matching native traces produce a genuine zero-boundary competitor. -/
theorem radial_three_piece_minimizer_energy_comparison {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (c : Domain n) {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (u w v : Domain n → Ambient q) (Du Dw Dv : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain c r) u Du)
    (hw : MemW12 ⟨{x | r < ‖x - c‖ ∧ ‖x - c‖ < s},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ w Dw)
    (hv : MemW12 (ballDomain c R) v Dv)
    (huN : TakesValuesIn N (ballDomain c r) u)
    (hwN : ∀ᵐ x ∂volume.restrict {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < s},
      w x ∈ N.carrierSet)
    (hvN : TakesValuesIn N (ballDomain c R) v)
    (hmin : IsLocallyEnergyMinimizing N Ω v Dv)
    (hclosedR : closedBall c R ⊆ Ω.val) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∀ (H : C(Icc (r / 2) r, Lp (Ambient q) 2 σ))
      (K : C(Icc r s, Lp (Ambient q) 2 σ))
      (L : C(Icc s ((s + R) / 2), Lp (Ambient q) 2 σ)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (r / 2) r,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + t • θ.val)) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + t • θ.val))) →
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r s,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + t • θ.val)) 2 σ,
          K ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + t • θ.val))) →
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo s ((s + R) / 2),
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => v (c + t • θ.val)) 2 σ,
          L ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => v (c + t • θ.val))) →
      H ⟨r, by linarith only [hr], le_rfl⟩ = K ⟨r, le_rfl, hrs.le⟩ →
      K ⟨s, hrs.le, le_rfl⟩ = L ⟨s, le_rfl, by linarith only [hsR]⟩ →
      (∫ x in ball c s, hsNormSq (Dv x)) ≤
        (∫ x in ball c r, hsNormSq (Du x)) +
          (∫ x in {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < s}, hsNormSq (Dw x)) := by
  intro σ H K L hH hK hL hmatchr hmatchs
  let f₁ : Domain n → Ambient q := fun x => if ‖x - c‖ < r then u x else w x
  let f : Domain n → Ambient q := fun x => if ‖x - c‖ < s then f₁ x else v x
  let Df : Domain n → Gradient n q := fun x i =>
    if ‖x - c‖ < s then (if ‖x - c‖ < r then Du x i else Dw x i) else Dv x i
  obtain ⟨hf, hE, hzero⟩ := memW12_radial_three_piece_gluing hn c hr hrs hsR
    u w v Du Dw Dv hu hw hv H K L hH hK hL hmatchr hmatchs
  have hf₁N : ∀ᵐ x ∂volume.restrict (ball c s), f₁ x ∈ N.carrierSet :=
    ae_radial_piecewise_property c hr hrs u w (fun z => z ∈ N.carrierSet) huN hwN
  have hAsub : {x : Domain n | s < ‖x - c‖ ∧ ‖x - c‖ < R} ⊆ ball c R :=
    fun _ hx => mem_ball_iff_norm.mpr hx.2
  have hvAN := ae_restrict_of_ae_restrict_of_subset hAsub hvN
  have hfN : TakesValuesIn N (ballDomain c R) f :=
    ae_radial_piecewise_property c (hr.trans hrs) hsR f₁ v
      (fun z => z ∈ N.carrierSet) hf₁N hvAN
  have hcmp := hmin c R (hr.trans (hrs.trans hsR)) hclosedR f Df hf hfN hzero
  have hcmpReal := ENNReal.toReal_mono hf.dirichletEnergy_ne_top hcmp
  have hvI : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c R) := hv.integrable_hsNormSq
  have hfI : IntegrableOn (fun x => hsNormSq (Df x)) (ball c R) := hf.integrable_hsNormSq
  change (dirichletEnergy Dv (ball c R)).toReal ≤ (dirichletEnergy Df (ball c R)).toReal at hcmpReal
  rw [dirichletEnergy_toReal hvI, dirichletEnergy_toReal hfI] at hcmpReal
  have hVB : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c s) :=
    hv.integrable_hsNormSq.mono_set (ball_subset_ball hsR.le)
  have hVA : IntegrableOn (fun x => hsNormSq (Dv x))
      {x : Domain n | s < ‖x - c‖ ∧ ‖x - c‖ < R} := hv.integrable_hsNormSq.mono_set hAsub
  have hsplit : (∫ x in ball c R, hsNormSq (Dv x)) =
      (∫ x in ball c s, hsNormSq (Dv x)) +
        (∫ x in {x : Domain n | s < ‖x - c‖ ∧ ‖x - c‖ < R}, hsNormSq (Dv x)) := by
    simpa only [ite_self] using integral_radial_piecewise c (hr.trans hrs) hsR
      (fun x => hsNormSq (Dv x)) (fun x => hsNormSq (Dv x)) hVB hVA
  rw [hsplit, hE] at hcmpReal
  linarith only [hcmpReal]

end StratificationTheory.Interpolation
