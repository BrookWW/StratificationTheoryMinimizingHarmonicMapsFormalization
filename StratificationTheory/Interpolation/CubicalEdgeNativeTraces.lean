module

public import StratificationTheory.Foundation.NativeIntervalL2Trace
public import StratificationTheory.Foundation.IntervalSobolevProductSpatialTrace
public import StratificationTheory.Interpolation.CubicalEdgeInterpolationTrace
public import StratificationTheory.Foundation.IntervalSobolevProductBase
public import StratificationTheory.Foundation.IntervalSobolevProductGluing

/-!
# Four native traces of the affine edge rectangle

The literal affine interpolation has native continuous L2 curves in both
coordinate directions. Its time endpoints retain the original line classes;
its spatial endpoints are the affine chords of the actual vertex values.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The same affine edge rectangle has both native flat trace curves. In
particular each spatial endpoint is the chord of that same pair of closed
line representatives, so shared raw vertices give shared whole edge traces. -/
theorem affine_edge_rectangle_native_four_traces {q : ℕ} {ε : ℝ} (hε : 0 < ε)
    {F G f h g k : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hh : MemLp h 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hk : MemLp k 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hFae : F =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] h)
    (hFinc : ∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
      G t - G s = ∫ y in s..t, k y) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let S : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let W : Domain 2 → Ambient q := fun y =>
      (1 - (e y).2 0 / ε) • F ((e y).1 0) + ((e y).2 0 / ε) • G ((e y).1 0)
    let chord : ℝ → Domain 1 → Ambient q := fun s x =>
      (1 - x 0 / ε) • F s + (x 0 / ε) • G s
    ∃ HT : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
      ∃ HS : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
      (∀ t : Icc (0 : ℝ) ε,
        ∃ ht : MemLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)))
          2 (volume.restrict S), HT t = ht.toLp
            (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)))) ∧
      (∃ h₀ : MemLp (fun x : Domain 1 => f (x 0)) 2 (volume.restrict S),
        HT ⟨0, le_rfl, hε.le⟩ = h₀.toLp (fun x : Domain 1 => f (x 0))) ∧
      (∃ h₁ : MemLp (fun x : Domain 1 => h (x 0)) 2 (volume.restrict S),
        HT ⟨ε, hε.le, le_rfl⟩ = h₁.toLp (fun x : Domain 1 => h (x 0))) ∧
      (∀ s : Icc (0 : ℝ) ε,
        ∃ hs : MemLp (fun x => W (e.symm (EuclideanSpace.single (0 : Fin 1) s.val, x)))
          2 (volume.restrict S), HS s = hs.toLp
            (fun x => W (e.symm (EuclideanSpace.single (0 : Fin 1) s.val, x)))) ∧
      (∃ h₀ : MemLp (chord 0) 2 (volume.restrict S),
        HS ⟨0, le_rfl, hε.le⟩ = h₀.toLp (chord 0)) ∧
      (∃ h₁ : MemLp (chord ε) 2 (volume.restrict S),
        HS ⟨ε, hε.le, le_rfl⟩ = h₁.toLp (chord ε)) ∧
      (∀ K : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
          ∃ hslice : MemLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
            2 (volume.restrict S), K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp
              (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) → K = HT) ∧
      ∀ K : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
        (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (0 : ℝ) ε,
          ∃ hslice : MemLp (fun x => W (e.symm (EuclideanSpace.single (0 : Fin 1) s, x)))
            2 (volume.restrict S), K ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp
              (fun x => W (e.symm (EuclideanSpace.single (0 : Fin 1) s, x)))) → K = HS := by
  intro e S W chord
  obtain ⟨T, _hTformula, hTraw, hT₀, hT₁, _hTunique⟩ :=
    affine_pair_continuous_lp_trace (volume.restrict (Ioo (0 : ℝ) ε)) hε
      hf hh hFae hGae
  obtain ⟨HT, hHTpull⟩ := exists_native_interval_continuous_L2_curve 0 ε T
  have hTrows : ∀ t : Icc (0 : ℝ) ε,
      ∃ ht : MemLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val)))
        2 (volume.restrict S), HT t = ht.toLp
          (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t.val))) := by
    intro t
    obtain ⟨ht, hteq⟩ := hTraw t
    have h := hHTpull t _ ht hteq
    simpa only [W, e.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero] using h
  have hTleft := hHTpull ⟨0, le_rfl, hε.le⟩ f hf hT₀
  have hTright := hHTpull ⟨ε, hε.le, le_rfl⟩ h hh hT₁
  let ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) ε)
  let A : ℝ → ℝ := fun t => t / ε
  let B : ℝ → ℝ := fun t => 1 - A t
  have hAtop : MemLp A ∞ ν := by
    apply memLp_top_of_bound (continuous_id.div_const ε).aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hlo : 0 ≤ A t := div_nonneg ht.1.le hε.le
    have hhi : A t ≤ 1 := (div_le_one hε).mpr ht.2.le
    change |A t| ≤ 1
    simpa only [abs_of_nonneg hlo] using hhi
  have hA : MemLp A 2 ν := hAtop.mono_exponent (by norm_num)
  have hB : MemLp B 2 ν := (memLp_const (1 : ℝ)).sub hA
  have hFcont := continuousOn_interval_of_integral_increments hε.le hg hFinc
  have hGcont := continuousOn_interval_of_integral_increments hε.le hk hGinc
  let CF : C(Icc (0 : ℝ) ε, Ambient q) := ⟨fun s => F s, hFcont.restrict⟩
  let CG : C(Icc (0 : ℝ) ε, Ambient q) := ⟨fun s => G s, hGcont.restrict⟩
  obtain ⟨L, hL⟩ := continuous_weighted_pair_lp_slices ν hA hB CF CG
  obtain ⟨HS, hHSpull⟩ := exists_native_interval_continuous_L2_curve 0 ε L
  have hSrows : ∀ s : Icc (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => W (e.symm (EuclideanSpace.single (0 : Fin 1) s.val, x)))
        2 (volume.restrict S), HS s = hs.toLp
          (fun x => W (e.symm (EuclideanSpace.single (0 : Fin 1) s.val, x))) := by
    intro s
    obtain ⟨hs, hseq⟩ := hL s
    have h := hHSpull s _ hs hseq
    simpa only [W, e.apply_symm_apply, PiLp.single_apply, ite_true,
      CF, CG, ContinuousMap.coe_mk, A, B] using h
  have hSleft : ∃ h₀ : MemLp (chord 0) 2 (volume.restrict S),
      HS ⟨0, le_rfl, hε.le⟩ = h₀.toLp (chord 0) := by
    simpa only [W, chord, e.apply_symm_apply, PiLp.single_apply, ite_true] using
      hSrows ⟨0, le_rfl, hε.le⟩
  have hSright : ∃ h₁ : MemLp (chord ε) 2 (volume.restrict S),
      HS ⟨ε, hε.le, le_rfl⟩ = h₁.toLp (chord ε) := by
    simpa only [W, chord, e.apply_symm_apply, PiLp.single_apply, ite_true] using
      hSrows ⟨ε, hε.le, le_rfl⟩
  refine ⟨HT, HS, hTrows, hTleft, hTright, hSrows, hSleft, hSright, ?_, ?_⟩
  · intro K hK
    exact continuous_lp_curves_eq_of_ae_interior_slices
      (volume.restrict S) hε HT K
      (f := fun p : Domain 1 × ℝ => W (e.symm (p.1, EuclideanSpace.single 0 p.2)))
      (Eventually.of_forall fun t ht => hTrows ⟨t, ht.1.le, ht.2.le⟩) hK
  · intro K hK
    exact continuous_lp_curves_eq_of_ae_interior_slices
      (volume.restrict S) hε HS K
      (f := fun p : Domain 1 × ℝ => W (e.symm (EuclideanSpace.single 0 p.2, p.1)))
      (Eventually.of_forall fun s hs => hSrows ⟨s, hs.1.le, hs.2.le⟩) hK

end StratificationTheory
