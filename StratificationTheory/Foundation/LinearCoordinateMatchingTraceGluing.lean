module

public import StratificationTheory.Foundation.LinearEquivSobolevInvariance
public import StratificationTheory.Foundation.CoordinateTraceWeakGluing

/-!
# Actual linear-coordinate weak gluing with matching native traces

Original full weak maps on both sides of a genuine linear coordinate seam
produce the same physical piecewise map and columns. Only their actual
original continuous native L2 trace classes are matched.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- Original physical weak pairs on two actual linear coordinate rectangles glue across an
actual common continuous native trace class, preserving the original piecewise pair. -/
theorem memW12_linear_piecewise_of_matching_L2_traces {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (Q : Domain (n + 1) ≃L[ℝ] Domain (n + 1))
    (u v : Domain (n + 1) → Ambient q) (Du Dv : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
      ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
    let Ω : ℝ → ℝ → OpenDomain (n + 1) := fun d f =>
      ⟨{y | (e y).1 ∈ U.val ∧ T y ∈ Ioo d f},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage T.continuous)⟩
    let R : ℝ → ℝ → OpenDomain (n + 1) := fun d f =>
      ⟨Q.symm ⁻¹' (Ω d f).val, (Ω d f).property.preimage Q.symm.continuous⟩
    MemW12 (R a b) u Du → MemW12 (R b c) v Dv →
    ∀ (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
      (K : C(Icc b c, Lp (Ambient q) 2 (volume.restrict U.val))),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hs : MemLp (fun x => u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2
            (volume.restrict U.val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b c,
        ∃ hs : MemLp (fun x => v (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2
            (volume.restrict U.val),
          K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => v (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
      H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbc.le⟩ →
      let f : Domain (n + 1) → Ambient q := fun y => if T (Q.symm y) < b then u y else v y
      let Df : Domain (n + 1) → Gradient (n + 1) q :=
        fun y i => if T (Q.symm y) < b then Du y i else Dv y i
      MemW12 (R a c) f Df ∧
      ∃ J : C(Icc a c, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ t : Icc a b, J ⟨t.val, t.property.1, t.property.2.trans hbc.le⟩ = H t) ∧
        (∀ t : Icc b c, J ⟨t.val, hab.le.trans t.property.1, t.property.2⟩ = K t) ∧
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hs : MemLp (fun x => f (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))
              2 (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ =
              hs.toLp (fun x => f (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) := by
  intro e T Ω R hu hv H K hH hK hMatch f Df
  have hpre (d z : ℝ) :
      (⟨Q ⁻¹' (R d z).val, (R d z).property.preimage Q.continuous⟩ : OpenDomain (n + 1)) =
        Ω d z := by
    apply Subtype.ext
    ext x
    change Q.symm (Q x) ∈ (Ω d z).val ↔ x ∈ (Ω d z).val
    rw [Q.symm_apply_apply]
  let pu := u ∘ Q
  let pv := v ∘ Q
  let pDu : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j • Du (Q x) j
  let pDv : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j • Dv (Q x) j
  have hu' : MemW12 (Ω a b) pu pDu := by
    simpa only [hpre] using memW12_continuousLinearEquiv_preimage Q hu
  have hv' : MemW12 (Ω b c) pv pDv := by
    simpa only [hpre] using memW12_continuousLinearEquiv_preimage Q hv
  let pf : Domain (n + 1) → Ambient q := fun x => if T x < b then pu x else pv x
  let pDf : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => if T x < b then pDu x i else pDv x i
  have hglue := memW12_coordinate_piecewise_of_matching_L2_traces (n := n) (q := q)
    U hab hbc pu pv pDu pDv hu' hv' H K hH hK hMatch
  have hpW : MemW12 (Ω a c) pf pDf := hglue.1
  have hf : f ∘ Q = pf := by
    funext x
    simp only [Function.comp_apply,f,pf,pu,pv,Q.symm_apply_apply]
  have hD : (fun x i => ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j •
      Df (Q x) j) = pDf := by
    funext x i
    by_cases ht : T x < b
    · simp only [Df,pDf,Q.symm_apply_apply,ht,if_true]
      rfl
    · simp only [Df,pDf,Q.symm_apply_apply,ht,if_false]
      rfl
  have hW : MemW12 (R a c) f Df := by
    apply (memW12_continuousLinearEquiv_preimage_iff Q).mp
    rw [hpre,hf,hD]
    exact hpW
  obtain ⟨J,hJL,hJR,hJ⟩ := hglue.2.2
  refine ⟨hW,J,hJL,hJR,?_⟩
  simpa only [pf,pu,pv,f,Function.comp_apply,Q.symm_apply_apply] using hJ

end StratificationTheory
