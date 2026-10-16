module

public import StratificationTheory.Foundation.SpatialConstantRectangle
public import StratificationTheory.Foundation.CoordinateTraceWeakGluing

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Actual spatial endpoint maps extend the same weak connector to a fixed
open time interval. The extension has zero outer time columns and agrees
pointwise with the original connector and all its columns on the original
open interpolation interval. -/
theorem memW12_constant_time_prism_extension {m q : ℕ} (U : OpenDomain m)
    [IsFiniteMeasure ((volume : Measure (Domain m)).restrict U.val)]
    (w : Fin 2 → Domain m → Ambient q) (Dw : Fin 2 → Domain m → Gradient m q)
    (hw : ∀ l, MemW12 U (w l) (Dw l))
    {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1)
    (W : Domain (m + 1) → Ambient q) (D : Domain (m + 1) → Gradient (m + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)
    let P : Domain (m + 1) →L[ℝ] Domain m :=
      (ContinuousLinearMap.fst ℝ (Domain m) (Domain 1)).comp e.toContinuousLinearMap
    let time := fun y : Domain (m + 1) => (e y).2 0
    let Ω := fun a b : ℝ => (⟨{y | P y ∈ U.val ∧ time y ∈ Ioo a b},
      (U.property.preimage P.continuous).inter (isOpen_Ioo.preimage
        ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_snd.comp e.continuous)))⟩ : OpenDomain (m + 1))
    let Ds := fun (l : Fin 2) (x : Domain (m + 1)) (i : Fin (m + 1)) =>
      Fin.lastCases (0 : Ambient q) (fun j => Dw l (P x) j) i
    let Vext := fun y : Domain (m + 1) =>
      if time y < 0 then w 0 (P y) else if time y < ε then W y else w 1 (P y)
    let Dext := fun (y : Domain (m + 1)) (i : Fin (m + 1)) =>
      if time y < 0 then Ds 0 y i else if time y < ε then D y i else Ds 1 y i
    MemW12 (Ω 0 ε) W D →
    ∀ H : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val)),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x : Domain m => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∃ hs : MemLp (w 0) 2 (volume.restrict U.val), H ⟨0, le_rfl, hε.le⟩ = hs.toLp (w 0)) →
    (∃ hs : MemLp (w 1) 2 (volume.restrict U.val), H ⟨ε, hε.le, le_rfl⟩ = hs.toLp (w 1)) →
    MemW12 (Ω (-1) 1) Vext Dext ∧
    (∀ y, time y ∈ Ioo (0 : ℝ) ε → Vext y = W y ∧ Dext y = D y) ∧
    (∫ y in (Ω 0 ε).val, hsNormSq (Dext y)) = ∫ y in (Ω 0 ε).val, hsNormSq (D y) := by
  classical
  intro e P time Ω Ds Vext Dext hW H hRaw hEnd₀ hEnd₁
  let H₀ : C(Icc (-1 : ℝ) 0, Lp (Ambient q) 2 (volume.restrict U.val)) :=
    ContinuousMap.const _ ((hw 0).2.1.toLp (w 0))
  let H₁ : C(Icc ε (1 : ℝ), Lp (Ambient q) 2 (volume.restrict U.val)) :=
    ContinuousMap.const _ ((hw 1).2.1.toLp (w 1))
  have hLift l a b : MemW12 (Ω a b) (w l ∘ P) (Ds l) :=
    memW12_spatial_constant_rectangle U (w l) (Dw l) (hw l) a b
  have hSlice (l : Fin 2) (t : ℝ) : (fun x : Domain m =>
      (w l ∘ P) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) = w l := by
    funext x
    change w l ((e (e.symm _)).1) = w l x
    rw [e.apply_symm_apply]
  have hRaw₀ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 0,
      ∃ hs : MemLp (fun x : Domain m => (w 0 ∘ P) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
        H₀ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => (w 0 ∘ P) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
    filter_upwards [] with t ht
    rw [hSlice]
    exact ⟨(hw 0).2.1, rfl⟩
  have hRaw₁ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo ε (1 : ℝ),
      ∃ hs : MemLp (fun x : Domain m => (w 1 ∘ P) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
        H₁ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => (w 1 ∘ P) (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) := by
    filter_upwards [] with t ht
    rw [hSlice]
    exact ⟨(hw 1).2.1, rfl⟩
  have hMatch₀ : H₀ ⟨0, by norm_num, le_rfl⟩ = H ⟨0, le_rfl, hε.le⟩ := by
    obtain ⟨hs, hEq⟩ := hEnd₀
    rw [hEq]
    rfl
  obtain ⟨hLeft, _hLeftE, J, _hJ₀, hJH, hJRaw⟩ :=
    memW12_coordinate_piecewise_of_matching_L2_traces U (by norm_num : (-1 : ℝ) < 0) hε
      (w 0 ∘ P) W (Ds 0) D (hLift 0 (-1) 0) hW H₀ H hRaw₀ hRaw hMatch₀
  let Wleft := fun y : Domain (m + 1) => if time y < 0 then w 0 (P y) else W y
  let Dleft := fun (y : Domain (m + 1)) (i : Fin (m + 1)) => if time y < 0 then Ds 0 y i else D y i
  have hMatch₁ : J ⟨ε, by linarith, le_rfl⟩ = H₁ ⟨ε, le_rfl, hεone.le⟩ := by
    rw [hJH ⟨ε, hε.le, le_rfl⟩]
    obtain ⟨hs, hEq⟩ := hEnd₁
    rw [hEq]
    rfl
  have hFinal := memW12_coordinate_piecewise_of_matching_L2_traces U
    (by linarith : (-1 : ℝ) < ε) hεone Wleft (w 1 ∘ P) Dleft (Ds 1)
    hLeft (hLift 1 ε 1) J H₁ hJRaw hRaw₁ hMatch₁
  have hValue : (fun y : Domain (m + 1) => if time y < ε then Wleft y else (w 1 ∘ P) y) = Vext := by
    funext y
    dsimp only [Vext, Wleft, Function.comp_apply]
    by_cases h0 : time y < 0
    · simp only [if_pos h0, if_pos (h0.trans hε)]
    · simp only [if_neg h0]
  have hColumns : (fun (y : Domain (m + 1)) (i : Fin (m + 1)) =>
      if time y < ε then Dleft y i else Ds 1 y i) = Dext := by
    funext y i
    dsimp only [Dext, Dleft]
    by_cases h0 : time y < 0
    · simp only [if_pos h0, if_pos (h0.trans hε)]
    · simp only [if_neg h0]
  have hTimeFormula (y : Domain (m + 1)) :
      ((EuclideanSpace.proj (0 : Fin 1)).comp
        ((ContinuousLinearMap.snd ℝ (Domain m) (Domain 1)).comp e.toContinuousLinearMap)) y = time y := rfl
  have hFull : MemW12 (Ω (-1) 1) Vext Dext := by
    convert hFinal.1 using 1
    · rfl
    · funext y
      change Vext y = (if ((EuclideanSpace.proj (0 : Fin 1)).comp
        ((ContinuousLinearMap.snd ℝ (Domain m) (Domain 1)).comp e.toContinuousLinearMap)) y < ε
          then Wleft y else (w 1 ∘ P) y)
      rw [hTimeFormula]
      exact congrFun hValue.symm y
    · funext y i
      change Dext y i = (if ((EuclideanSpace.proj (0 : Fin 1)).comp
        ((ContinuousLinearMap.snd ℝ (Domain m) (Domain 1)).comp e.toContinuousLinearMap)) y < ε
          then Dleft y i else Ds 1 y i)
      rw [hTimeFormula]
      exact congrFun (congrFun hColumns.symm y) i
  have hPoint y (hy : time y ∈ Ioo (0 : ℝ) ε) : Vext y = W y ∧ Dext y = D y := by
    constructor
    · simp only [Vext, if_neg (not_lt.mpr hy.1.le), if_pos hy.2]
    · funext i
      simp only [Dext, if_neg (not_lt.mpr hy.1.le), if_pos hy.2]
  refine ⟨hFull, hPoint, ?_⟩
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (Ω 0 ε).property.measurableSet] with y hy
  rw [(hPoint y hy.2).2]

end StratificationTheory
