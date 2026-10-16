module

public import StratificationTheory.Foundation.LinearEquivSobolevPullback

/-!
# Exact linear coordinate invariance of original weak graphs

The actual inverse coordinate columns cancel the original forward columns.
This gives both directions of full Sobolev transport for the same original
map and gradient, without any transformed weak-graph hypothesis.
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped BigOperators
namespace StratificationTheory

theorem continuousLinearEquiv_inverse_gradient_columns {n q : ℕ}
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

/-- The original full weak graph is equivalent to its actual full linear
pullback with exactly the forward chain-rule columns. -/
theorem memW12_continuousLinearEquiv_preimage_iff {n q : ℕ}
    (Q : Domain n ≃L[ℝ] Domain n) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q} :
    MemW12 ⟨Q ⁻¹' Ω.val,Ω.property.preimage Q.continuous⟩ (u ∘ Q)
      (fun x i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (Q x) j) ↔
        MemW12 Ω u Du := by
  constructor
  · intro h
    have hb := memW12_continuousLinearEquiv_preimage Q.symm h
    have hΩ : (⟨Q.symm ⁻¹' (Q ⁻¹' Ω.val),
        (Ω.property.preimage Q.continuous).preimage Q.symm.continuous⟩ : OpenDomain n) = Ω := by
      apply Subtype.ext
      ext x
      change Q (Q.symm x) ∈ Ω.val ↔ x ∈ Ω.val
      rw [Q.apply_symm_apply]
    have hf : (u ∘ Q) ∘ Q.symm = u := by
      funext x
      simp only [Function.comp_apply,Q.apply_symm_apply]
    have hD : (fun x i => ∑ j : Fin n, (Q.symm (EuclideanSpace.single i 1)) j •
        (∑ k : Fin n, (Q (EuclideanSpace.single j 1)) k • Du (Q (Q.symm x)) k)) = Du := by
      funext x i
      rw [Q.apply_symm_apply]
      exact continuousLinearEquiv_inverse_gradient_columns Q (Du x) i
    change MemW12 _ ((u ∘ Q) ∘ Q.symm)
      (fun x i => ∑ j : Fin n, (Q.symm (EuclideanSpace.single i 1)) j •
        (∑ k : Fin n, (Q (EuclideanSpace.single j 1)) k • Du (Q (Q.symm x)) k)) at hb
    rw [hΩ,hf,hD] at hb
    exact hb
  · exact memW12_continuousLinearEquiv_preimage Q

end StratificationTheory

