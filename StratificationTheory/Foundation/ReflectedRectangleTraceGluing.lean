module

public import StratificationTheory.Foundation.LinearEquivSobolevPullback
public import StratificationTheory.Foundation.CoordinateTraceWeakGluing

/-!
# Actual reflected weak rectangles with common native endpoint traces

Two original positive normal rectangles with a common continuous native L2
endpoint produce the actual reflected-left and original-right weak map on
one two-sided normal rectangle.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Original full positive weak rectangles and their actual native curves
produce a full weak graph of the same reflected two-sided map. -/
theorem exists_reflected_rectangle_weak_gluing {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (u v : Domain (n + 1) → Ambient q) (Du Dv : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω : ℝ → ℝ → OpenDomain (n + 1) := fun a b =>
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let R : Domain (n + 1) → Domain (n + 1) := fun y => e.symm ((e y).1,-(e y).2)
    MemW12 (Ω 0 α) u Du → MemW12 (Ω 0 β) v Dv →
    ∀ (H : C(Icc (0 : ℝ) α,Lp (Ambient q) 2 (volume.restrict U.val)))
      (K : C(Icc (0 : ℝ) β,Lp (Ambient q) 2 (volume.restrict U.val))),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) α,
      ∃ hs : MemLp (fun x => u (e.symm (x,EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict U.val),
        H ⟨t,ht.1.le,ht.2.le⟩ = hs.toLp (fun x => u (e.symm
          (x,EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) β,
      ∃ hs : MemLp (fun x => v (e.symm (x,EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict U.val),
        K ⟨t,ht.1.le,ht.2.le⟩ = hs.toLp (fun x => v (e.symm
          (x,EuclideanSpace.single (0 : Fin 1) t)))) →
    H ⟨0,le_rfl,hα.le⟩ = K ⟨0,le_rfl,hβ.le⟩ →
    ∃ δ : ℝ, ∃ _hδ : 0 < δ, ∃ D : Domain (n + 1) → Gradient (n + 1) q,
      MemW12 (Ω (-δ) δ) (fun y => if (e y).2 0 < 0 then u (R y) else v y) D := by
  intro e Ω R hu hv H K hH hK hMatch
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  let σ : Domain 1 ≃L[ℝ] Domain 1 :=
    (Units.mk0 (-1 : ℝ) (by norm_num)) • ContinuousLinearEquiv.refl ℝ (Domain 1)
  let Q := (e.trans (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n)) σ)).trans e.symm
  have hQ (x : Domain (n + 1)) : Q x = R x := by
    change e.symm ((e x).1,(-1 : ℝ) • (e x).2) = _
    simp only [R,neg_one_smul]
  have hPre : (⟨Q ⁻¹' (Ω 0 α).val,(Ω 0 α).property.preimage Q.continuous⟩ : OpenDomain (n + 1)) =
      Ω (-α) 0 := by
    apply Subtype.ext
    ext y
    simp only [mem_preimage,Ω,mem_setOf_eq,hQ,R,e.apply_symm_apply,PiLp.neg_apply]
    constructor
    · intro h
      exact ⟨h.1,by linarith only [h.2.2],by linarith only [h.2.1]⟩
    · intro h
      exact ⟨h.1,by linarith only [h.2.2],by linarith only [h.2.1]⟩
  let Dleft : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j • Du (Q x) j
  have hLeft₀ : MemW12 (Ω (-α) 0) (u ∘ R) Dleft := by
    have h := memW12_continuousLinearEquiv_preimage Q hu
    change MemW12 _ (u ∘ Q) Dleft at h
    have huQ : u ∘ Q = u ∘ R := by funext x; rw [Function.comp_apply,hQ]; rfl
    rw [hPre,huQ] at h
    exact h
  have hLeftSub : (Ω (-δ) 0).val ⊆ (Ω (-α) 0).val := by
    intro y hy
    exact ⟨hy.1,lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hy.2.1,hy.2.2⟩
  have hRightSub : (Ω 0 δ).val ⊆ (Ω 0 β).val := by
    intro y hy
    exact ⟨hy.1,hy.2.1,hy.2.2.trans_le (min_le_right _ _)⟩
  have hLeft : MemW12 (Ω (-δ) 0) (u ∘ R) Dleft :=
    ⟨hLeft₀.1.mono hLeftSub,hLeft₀.2.1.mono_measure (Measure.restrict_mono_set volume hLeftSub),
      fun i => (hLeft₀.2.2 i).mono_measure (Measure.restrict_mono_set volume hLeftSub)⟩
  have hRight : MemW12 (Ω 0 δ) v Dv :=
    ⟨hv.1.mono hRightSub,hv.2.1.mono_measure (Measure.restrict_mono_set volume hRightSub),
      fun i => (hv.2.2 i).mono_measure (Measure.restrict_mono_set volume hRightSub)⟩
  let ιL : C(Icc (-δ) (0 : ℝ),Icc (0 : ℝ) α) :=
    ⟨fun t => ⟨-t.val,by linarith only [t.property.2],
      by have ht := t.property.1; have hd := min_le_left α β; dsimp only [δ] at ht; linarith⟩,
      continuous_subtype_val.neg.subtype_mk _⟩
  let ιR : C(Icc (0 : ℝ) δ,Icc (0 : ℝ) β) :=
    ⟨fun t => ⟨t.val,t.property.1,t.property.2.trans (min_le_right _ _)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let HL := H.comp ιL
  let KR := K.comp ιR
  have hHL : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-δ) (0 : ℝ),
      ∃ hs : MemLp (fun x => (u ∘ R) (e.symm (x,EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict U.val),
        HL ⟨t,ht.1.le,ht.2.le⟩ = hs.toLp (fun x => (u ∘ R) (e.symm
          (x,EuclideanSpace.single (0 : Fin 1) t))) := by
    have hPull := ((volume : Measure ℝ).quasiMeasurePreserving_smul
      (by norm_num : (-1 : ℝ) ≠ 0)).ae hH
    filter_upwards [hPull] with t ht htI
    have hn : -t ∈ Ioo (0 : ℝ) α :=
      ⟨by linarith only [htI.2],by have hd := min_le_left α β; dsimp only [δ] at htI; linarith only [htI.1,hd]⟩
    have h := ht (by simpa only [smul_eq_mul,neg_one_mul] using hn)
    have hR (x : Domain n) : R (e.symm (x,EuclideanSpace.single (0 : Fin 1) t)) =
        e.symm (x,EuclideanSpace.single (0 : Fin 1) (-t)) := by
      dsimp only [R]
      rw [e.apply_symm_apply]
      exact congrArg (fun z : Domain 1 => e.symm (x,z)) (PiLp.single_neg 2 0).symm
    change ∃ hs : MemLp (fun x => u (R (e.symm (x,EuclideanSpace.single (0 : Fin 1) t))))
        2 (volume.restrict U.val),
      H ⟨-t,hn.1.le,hn.2.le⟩ = hs.toLp (fun x => u (R (e.symm (x,EuclideanSpace.single (0 : Fin 1) t))))
    simp only [hR]
    simpa only [smul_eq_mul,neg_one_mul] using h
  have hKR : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) δ,
      ∃ hs : MemLp (fun x => v (e.symm (x,EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict U.val),
        KR ⟨t,ht.1.le,ht.2.le⟩ = hs.toLp (fun x => v (e.symm
          (x,EuclideanSpace.single (0 : Fin 1) t))) := by
    filter_upwards [hK] with t ht htI
    exact ht ⟨htI.1,htI.2.trans_le (min_le_right _ _)⟩
  have hMatch' : HL ⟨0,(neg_nonpos.mpr hδ.le),le_rfl⟩ = KR ⟨0,le_rfl,hδ.le⟩ := by
    change H ⟨-(0 : ℝ),by norm_num,by simpa only [neg_zero] using hα.le⟩ =
      K ⟨0,le_rfl,hβ.le⟩
    simpa only [neg_zero] using hMatch
  have hGlue := memW12_coordinate_piecewise_of_matching_L2_traces U
    (a := -δ) (b := 0) (c := δ) (neg_neg_of_pos hδ) hδ
    (u ∘ R) v Dleft Dv hLeft hRight HL KR hHL hKR hMatch'
  exact ⟨δ,hδ,_,hGlue.1⟩

end StratificationTheory
