module

public import StratificationTheory.Frozen.RadialTraceGluing
public import StratificationTheory.Foundation.RadialPiecewiseTrace
public import StratificationTheory.Interpolation.CollarAdmissibility

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Two matching native trace interfaces produce a genuine three-piece
Sobolev competitor with exact energy addition and zero outer boundary
difference from the original exterior map. -/
theorem memW12_radial_three_piece_gluing {n q : ℕ} (hn : 2 ≤ n)
    (c : Domain n) {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (u w v : Domain n → Ambient q) (Du Dw Dv : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain c r) u Du)
    (hw : MemW12 ⟨{x | r < ‖x - c‖ ∧ ‖x - c‖ < s},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ w Dw)
    (hv : MemW12 (ballDomain c R) v Dv) :
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
      let f : Domain n → Ambient q := fun x =>
        if ‖x - c‖ < s then (if ‖x - c‖ < r then u x else w x) else v x
      let Df : Domain n → Gradient n q := fun x i =>
        if ‖x - c‖ < s then (if ‖x - c‖ < r then Du x i else Dw x i) else Dv x i
      MemW12 (ballDomain c R) f Df ∧
        (∫ x in ball c R, hsNormSq (Df x)) =
          (∫ x in ball c r, hsNormSq (Du x)) +
            (∫ x in {x : Domain n | r < ‖x - c‖ ∧ ‖x - c‖ < s}, hsNormSq (Dw x)) +
              (∫ x in {x : Domain n | s < ‖x - c‖ ∧ ‖x - c‖ < R}, hsNormSq (Dv x)) ∧
        HasZeroBoundaryDifference (ballDomain c R) v Dv f Df := by
  intro σ H K L hH hK hL hmatchr hmatchs f Df
  let A : OpenDomain n := ⟨{x | s < ‖x - c‖ ∧ ‖x - c‖ < R},
    isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩
  have hAsub : A.val ⊆ (ballDomain c R).val := fun _ hx => mem_ball_iff_norm.mpr hx.2
  have hvA : MemW12 A v Dv :=
    ⟨hv.1.mono hAsub, hv.2.1.mono_measure (Measure.restrict_mono_set volume hAsub),
      fun i => (hv.2.2 i).mono_measure (Measure.restrict_mono_set volume hAsub)⟩
  let iK : C(Icc r ((r + s) / 2), Icc r s) :=
    ⟨fun t => ⟨t.val, t.property.1, t.property.2.trans (by linarith only [hrs])⟩,
      continuous_subtype_val.subtype_mk _⟩
  let K₁ := K.comp iK
  have hK₁ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r ((r + s) / 2),
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + t • θ.val)) 2 σ,
        K₁ ⟨t, ht.1.le, ht.2.le⟩ =
          hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + t • θ.val)) := by
    filter_upwards [hK] with t hKt ht
    exact hKt ⟨ht.1, ht.2.trans_le (by linarith only [hrs])⟩
  have hmatch₁ : H ⟨r, by linarith only [hr], le_rfl⟩ =
      K₁ ⟨r, le_rfl, by linarith only [hrs]⟩ := hmatchr
  have hglue₁ := memW12_radial_trace_gluing hn c hr hrs u w Du Dw hu hw H K₁ hH hK₁ hmatch₁
  let f₁ : Domain n → Ambient q := fun x => if ‖x - c‖ < r then u x else w x
  let D₁ : Domain n → Gradient n q := fun x i => if ‖x - c‖ < r then Du x i else Dw x i
  have hf₁ : MemW12 (ballDomain c s) f₁ D₁ := hglue₁.1
  obtain ⟨J, _hJleft, hJright, hJtrace⟩ := exists_radial_trace_piecewise c σ
    (by linarith only [hr] : 0 < r / 2) (by linarith only [hr] : r / 2 < r)
    hrs u w H K hH hK hmatchr
  let iJ : C(Icc (s / 2) s, Icc (r / 2) s) :=
    ⟨fun t => ⟨t.val, (show r / 2 ≤ s / 2 by linarith only [hrs]).trans t.property.1,
      t.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  let H₂ := J.comp iJ
  have hH₂ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (s / 2) s,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => f₁ (c + t • θ.val)) 2 σ,
        H₂ ⟨t, ht.1.le, ht.2.le⟩ =
          hslice.toLp (fun θ : sphere (0 : Domain n) 1 => f₁ (c + t • θ.val)) := by
    filter_upwards [hJtrace] with t hJt ht
    exact hJt ⟨(show r / 2 ≤ s / 2 by linarith only [hrs]).trans_lt ht.1, ht.2⟩
  have hmatch₂ : H₂ ⟨s, by linarith only [hr, hrs], le_rfl⟩ =
      L ⟨s, le_rfl, by linarith only [hsR]⟩ :=
    (hJright ⟨s, hrs.le, le_rfl⟩).trans hmatchs
  have hglue₂ := memW12_radial_trace_gluing hn c (hr.trans hrs) hsR
    f₁ v D₁ Dv hf₁ hvA H₂ L hH₂ hL hmatch₂
  have hf : MemW12 (ballDomain c R) f Df := hglue₂.1
  refine ⟨hf, ?_, ?_⟩
  · exact hglue₂.2.trans (congrArg
      (fun z : ℝ => z + ∫ x in A.val, hsNormSq (Dv x)) hglue₁.2)
  · apply Interpolation.zeroBoundaryDifference_of_ae_eq_outer_collar
      (hr.trans (hrs.trans hsR)) (hr.trans hrs).le hsR hv hf
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_closedBall)] with x hx
    have hxs : s < ‖x - c‖ := lt_of_not_ge fun h => hx.2 (mem_closedBall_iff_norm.mpr h)
    change v x = if ‖x - c‖ < s then (if ‖x - c‖ < r then u x else w x) else v x
    rw [if_neg hxs.not_gt]

end StratificationTheory
