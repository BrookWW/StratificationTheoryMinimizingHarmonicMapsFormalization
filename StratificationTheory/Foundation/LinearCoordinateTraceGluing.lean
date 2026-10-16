module

public import StratificationTheory.Foundation.LinearEquivSobolevPullback
public import StratificationTheory.Foundation.CoordinateTraceLimitGluing

/-!
# Weak gluing in actual linear normal coordinates

Genuine continuous linear coordinate charts transport original one-sided
weak graphs. A common limit of the actual raw slices identifies their traces
and produces the same physical piecewise graph.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

private theorem source_linear_equiv_inverse_columns {n q : ℕ}
    (Q : Domain n ≃L[ℝ] Domain n) (A : Gradient n q) (i : Fin n) :
    (∑ j : Fin n, (Q.symm (EuclideanSpace.single i 1)) j •
      (∑ k : Fin n, (Q (EuclideanSpace.single j 1)) k • A k)) = A i := by
  have hbasis (v : Domain n) : ∑ j : Fin n, v j • EuclideanSpace.single j 1 = v := by
    ext k
    simp [Pi.single_apply]
  have hcoef (k : Fin n) :
      (∑ j : Fin n, (Q.symm (EuclideanSpace.single i 1)) j *
        (Q (EuclideanSpace.single j 1)) k) = (EuclideanSpace.single i 1 : Domain n) k := by
    have hx : (∑ j : Fin n, (Q.symm (EuclideanSpace.single i 1)) j •
        Q (EuclideanSpace.single j 1)) = EuclideanSpace.single i 1 := by
      have hh := congrArg Q (hbasis (Q.symm (EuclideanSpace.single i 1)))
      simpa only [map_sum, map_smul, Q.apply_symm_apply] using hh
    have h := congrArg (EuclideanSpace.proj (𝕜 := ℝ) k) hx
    simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.proj, PiLp.proj_apply] using h
  calc
    _ = ∑ k : Fin n, (∑ j : Fin n, (Q.symm (EuclideanSpace.single i 1)) j *
        (Q (EuclideanSpace.single j 1)) k) • A k := by
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = ∑ k : Fin n, (EuclideanSpace.single i 1 : Domain n) k • A k := by simp_rw [hcoef]
    _ = A i := by simp [PiLp.single_apply]

/-- Actual linear-chart raw limits produce full weak gluing of the original
physical maps and columns. -/
theorem memW12_linear_piecewise_of_common_raw_L2_limit {n q : ℕ} (U : OpenDomain n)
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
    ∀ g : Domain n → Ambient q, ∀ hg : MemLp g 2 (volume.restrict U.val),
      Tendsto (fun t => eLpNorm (fun x : Domain n =>
        u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) - g x)
          2 (volume.restrict U.val)) (𝓝[<] b) (𝓝 0) →
      Tendsto (fun t => eLpNorm (fun x : Domain n =>
        v (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) - g x)
          2 (volume.restrict U.val)) (𝓝[>] b) (𝓝 0) →
      let f : Domain (n + 1) → Ambient q := fun y => if T (Q.symm y) < b then u y else v y
      let Df : Domain (n + 1) → Gradient (n + 1) q :=
        fun y i => if T (Q.symm y) < b then Du y i else Dv y i
      MemW12 (R a c) f Df ∧
      ∃ J : C(Icc a c, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hs : MemLp (fun x => f (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))
              2 (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ =
              hs.toLp (fun x => f (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        J ⟨b, hab.le, hbc.le⟩ = hg.toLp g := by
  intro e T Ω R hu hv g hg hleft hright f Df
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
  have hglue := memW12_coordinate_piecewise_of_common_raw_L2_limit (n := n) (q := q)
    U hab hbc pu pv pDu pDv hu' hv' g hg hleft hright
  have hpW : MemW12 (Ω a c) pf pDf := hglue.1
  have hback := memW12_continuousLinearEquiv_preimage Q.symm hpW
  have hf : pf ∘ Q.symm = f := by
    funext x
    simp only [Function.comp_apply, pf, pu, pv, f, Q.apply_symm_apply]
  have hD : (fun x i => ∑ j : Fin (n + 1), (Q.symm (EuclideanSpace.single i 1)) j •
      pDf (Q.symm x) j) = Df := by
    funext x i
    dsimp only [pDf, pDu, pDv, Df]
    by_cases ht : T (Q.symm x) < b
    · simp only [ht, if_true, Q.apply_symm_apply]
      exact source_linear_equiv_inverse_columns Q (Du x) i
    · simp only [ht, if_false, Q.apply_symm_apply]
      exact source_linear_equiv_inverse_columns Q (Dv x) i
  have hW : MemW12 (R a c) f Df := by
    change MemW12 (R a c) (pf ∘ Q.symm)
      (fun x i => ∑ j : Fin (n + 1), (Q.symm (EuclideanSpace.single i 1)) j •
        pDf (Q.symm x) j) at hback
    rw [hf,hD] at hback
    exact hback
  obtain ⟨J,hJ,hJend⟩ := hglue.2.2
  refine ⟨hW,J,?_,hJend⟩
  simpa only [pf,pu,pv,f,Function.comp_apply,Q.symm_apply_apply] using hJ

end StratificationTheory

