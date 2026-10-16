module

public import StratificationTheory.Foundation.SpatialConeCanonicalNormalTrace
public import StratificationTheory.Foundation.SpatialConeNormalSymmetry
public import StratificationTheory.Foundation.ReflectedRectangleTraceGluing

/-!
# Original two spatial cones form a full weak seam with independent time

Original face-times-time weak graphs with a common original flat edge class
produce the actual two-cone weak map across the spatial seam. Spatial normal
coordinates and the actual spatial swap retain interpolation time throughout.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StratificationTheory

/-- Two original flat face weak graphs and their common original trace
produce a genuine two-cone full weak graph on every compact lateral patch. -/
theorem exists_original_spatial_two_cone_weak_gluing {n q : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ i : Fin n, |x i| < 1)
    {a b₀ b₁ c d : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hb₁ : b₁ < 2)
    (w : Fin 2 → Domain (n + 1 + 1) → Ambient q)
    (Dw : Fin 2 → Domain (n + 1 + 1) → Gradient (n + 1 + 1) q) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let B : OpenDomain (n + 1) :=
      ⟨⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let Ω : OpenDomain (n + 1 + 1) :=
      ⟨{z | (e z).1 ∈ B.val ∧ (e z).2 0 ∈ Ioo c d},
        (B.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    (∀ l : Fin 2, MemW12 Ω (w l) (Dw l)) →
    let μ := ((volume : Measure (Domain n)).restrict S).prod (volume.restrict (Ioo c d))
    let f : Fin 2 → (Domain n × ℝ) × ℝ → Ambient q := fun l p =>
      w l (e.symm (b.symm (p.1.1,EuclideanSpace.single (0 : Fin 1) p.2),
        EuclideanSpace.single (0 : Fin 1) p.1.2))
    ∀ H : Fin 2 → C(Icc a 1,Lp (Ambient q) 2 μ),
    (∀ l, AEStronglyMeasurable (f l) (μ.prod (volume.restrict (Ioo a 1)))) →
    (∀ l : Fin 2, ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f l (x,z)) 2 μ,
        H l ⟨z,hz.1.le,hz.2.le⟩ = hs.toLp (fun x => f l (x,z))) →
    ∀ g : Domain n × ℝ → Ambient q, ∀ hg : MemLp g 2 μ,
      (∀ l : Fin 2, H l ⟨1,ha.le,le_rfl⟩ = hg.toLp g) →
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let V := {y : Domain (n + 1 + 1) | (e y).1 ∈ C ∧ (e y).2 0 ∈ Ioo c d}
    let Fcone : Domain (n + 1 + 1 + 1) → Domain (n + 1 + 1) := fun y =>
      e.symm ((((e (eF y).1).2 0)⁻¹ • (e (eF y).1).1),(eF y).2)
    let W := fun l : Fin 2 => w l ∘ Fcone
    ∃ (F S₀ : Domain (n + 1 + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1 + 1)),
      (∀ y η, F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n) ∧
      (∀ z, S₀ z = eF.symm
        (cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true (eF z).1,(eF z).2)) ∧
      ∀ U : OpenDomain (n + 1 + 1), IsCompact (closure U.val) → closure U.val ⊆ interior V →
      ∃ δ : ℝ, ∃ _hδ : 0 < δ,
      ∃ D : Domain (n + 1 + 1 + 1) → Gradient (n + 1 + 1 + 1) q,
        MemW12
          ⟨{z | (eF (F.symm z)).1 ∈ U.val ∧ (eF (F.symm z)).2 0 ∈ Ioo (-δ) δ},
            (U.property.preimage (continuous_fst.comp (eF.continuous.comp F.symm.continuous))).inter
              (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
                (continuous_snd.comp (eF.continuous.comp F.symm.continuous))))⟩
          (fun z => if (eF (F.symm z)).2 0 < 0 then W 0 (S₀ z) else W 1 z) D := by
  intro b e eF B Ω hw μ f H hf hSlices g hg hEnd T ξ C V Fcone W
  obtain ⟨F₀,hF₀,hData₀⟩ := exists_canonical_spatial_cone_normal_trace hS hSbound ha hb₀ hb₁
    (w 0) (Dw 0) (hw 0) (H 0) (hf 0) (hSlices 0) g hg (hEnd 0)
  obtain ⟨F₁,hF₁,hData₁⟩ := exists_canonical_spatial_cone_normal_trace hS hSbound ha hb₀ hb₁
    (w 1) (Dw 1) (hw 1) (H 1) (hf 1) (hSlices 1) g hg (hEnd 1)
  have hEq : F₀ = F₁ := spatial_cone_normal_linear_chart_unique F₀ F₁ hF₀ hF₁
  subst F₁
  have hF : ∀ (y : Domain (n + 1 + 1)) (η : ℝ),
      F₀ (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n := hF₀
  obtain ⟨S₀,hS₀,_hSS,_hTime,hSwap⟩ := exists_spatial_cone_normal_swap n
  refine ⟨F₀,S₀,hF,hS₀,?_⟩
  intro U hK hUV
  have hUfinite : (volume : Measure (Domain (n + 1 + 1))) U.val ≠ ⊤ :=
    ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono subset_closure)
  letI : IsFiniteMeasure ((volume : Measure (Domain (n + 1 + 1))).restrict U.val) :=
    isFiniteMeasure_restrict.mpr hUfinite
  obtain ⟨α,hα,hWeak₀,J₀,⟨hJ₀,hG₀,hEnd₀⟩,_hUnique₀⟩ := hData₀ U hK hUV
  obtain ⟨β,hβ,hWeak₁,J₁,⟨hJ₁,hG₁,hEnd₁⟩,_hUnique₁⟩ := hData₁ U hK hUV
  have hMatch : J₀ ⟨0,le_rfl,hα.le⟩ = J₁ ⟨0,le_rfl,hβ.le⟩ := hEnd₀.trans hEnd₁.symm
  obtain ⟨δ,hδ,Dg,hWg⟩ := exists_reflected_rectangle_weak_gluing U hα hβ
    (W 0 ∘ F₀) (W 1 ∘ F₀) _ _ hWeak₀ hWeak₁ J₀ J₁ hJ₀ hJ₁ hMatch
  let Rnormal : Domain (n + 1 + 1 + 1) → Domain (n + 1 + 1 + 1) :=
    fun z => eF.symm ((eF z).1,-(eF z).2)
  let pW : Domain (n + 1 + 1 + 1) → Ambient q := fun z =>
    if (eF z).2 0 < 0 then W 0 (F₀ (Rnormal z)) else W 1 (F₀ z)
  have hpW : MemW12
      ⟨{z | (eF z).1 ∈ U.val ∧ (eF z).2 0 ∈ Ioo (-δ) δ},
        (U.property.preimage (continuous_fst.comp eF.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp eF.continuous)))⟩ pW Dg := hWg
  have hsingle (t : Domain 1) : EuclideanSpace.single (0 : Fin 1) (t 0) = t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply,ite_true]
  have hSwapF (y : Domain (n + 1 + 1)) (η : ℝ) :
      S₀ (F₀ (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η))) =
        F₀ (eF.symm (y,EuclideanSpace.single (0 : Fin 1) (-η))) := by
    rw [hF,hSwap,hF]
  have hPoint (z : Domain (n + 1 + 1 + 1)) : F₀ (Rnormal z) = S₀ (F₀ z) := by
    have h := hSwapF (eF z).1 ((eF z).2 0)
    have hRep : eF.symm ((eF z).1,EuclideanSpace.single (0 : Fin 1) ((eF z).2 0)) = z := by
      rw [hsingle,eF.symm_apply_apply]
    have hNeg : eF.symm ((eF z).1,EuclideanSpace.single (0 : Fin 1) (-((eF z).2 0))) = Rnormal z := by
      change eF.symm ((eF z).1,EuclideanSpace.single (0 : Fin 1) (-((eF z).2 0))) =
        eF.symm ((eF z).1,-(eF z).2)
      apply congrArg (fun v : Domain 1 => eF.symm ((eF z).1,v))
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.single_apply,PiLp.neg_apply,ite_true]
    rw [hRep,hNeg] at h
    exact h.symm
  have hFunc : pW ∘ F₀.symm =
      (fun z => if (eF (F₀.symm z)).2 0 < 0 then W 0 (S₀ z) else W 1 z) := by
    funext z
    change (if (eF (F₀.symm z)).2 0 < 0 then W 0 (F₀ (Rnormal (F₀.symm z)))
      else W 1 (F₀ (F₀.symm z))) = _
    rw [hPoint,F₀.apply_symm_apply]
  have hBack := memW12_continuousLinearEquiv_preimage F₀.symm hpW
  rw [hFunc] at hBack
  exact ⟨δ,hδ,_,hBack⟩

end StratificationTheory
