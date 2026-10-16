module

public import StratificationTheory.Foundation.IsometricDomainSobolevPullback
public import StratificationTheory.Foundation.CoordinateTraceLimitGluing

/-!
# Full weak gluing across isometric flat seams

Original weak pairs on two rotated rectangles glue across a common genuine
raw L2 limit. The resulting map and columns are the literal original physical
piecewise pair, and their native HS energy is exactly additive.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

private theorem source_isometry_inverse_columns {n q : ℕ}
    (Q : Domain n ≃ₗᵢ[ℝ] Domain n) (A : Gradient n q) (i : Fin n) :
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

/-- Original physical weak pairs on two rotated rectangles glue across an
actual common raw normal-slice limit, preserving the original piecewise pair. -/
theorem memW12_isometric_piecewise_of_common_raw_L2_limit {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (Q : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1))
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
      (∫ y in (R a c).val, hsNormSq (Df y)) =
        (∫ y in (R a b).val, hsNormSq (Du y)) + (∫ y in (R b c).val, hsNormSq (Dv y)) ∧
      ∃ J : C(Icc a c, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hs : MemLp (fun x => f (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))
              2 (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ =
              hs.toLp (fun x => f (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        J ⟨b, hab.le, hbc.le⟩ = hg.toLp g := by
  intro e T Ω R hu hv g hg hleft hright f Df
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := isFiniteMeasure_restrict.mp inferInstance
  have hfinite (d z : ℝ) : (volume : Measure (Domain (n + 1))) (Ω d z).val ≠ ⊤ := by
    change (volume : Measure (Domain (n + 1)))
      {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo d z} ≠ ⊤
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  have hRfinite (d z : ℝ) : (volume : Measure (Domain (n + 1))) (R d z).val ≠ ⊤ := by
    change (volume : Measure (Domain (n + 1))) (Q.symm ⁻¹' (Ω d z).val) ≠ ⊤
    rw [Q.symm.measurePreserving.measure_preimage (Ω d z).property.measurableSet.nullMeasurableSet]
    exact hfinite d z
  have hpre (d z : ℝ) :
      (⟨Q ⁻¹' (R d z).val, (R d z).property.preimage Q.continuous⟩ : OpenDomain (n + 1)) = Ω d z := by
    apply Subtype.ext
    ext x
    change Q.symm (Q x) ∈ (Ω d z).val ↔ x ∈ (Ω d z).val
    rw [Q.symm_apply_apply]
  have hset (d z : ℝ) : Q ⁻¹' (R d z).val = (Ω d z).val := congrArg Subtype.val (hpre d z)
  let pu := u ∘ Q
  let pv := v ∘ Q
  let pDu : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j • Du (Q x) j
  let pDv : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => ∑ j : Fin (n + 1), (Q (EuclideanSpace.single i 1)) j • Dv (Q x) j
  have hpu := memW12_isometric_preimage_energy (hRfinite a b) hu Q
  have hpv := memW12_isometric_preimage_energy (hRfinite b c) hv Q
  have hu' : MemW12 (Ω a b) pu pDu := by simpa only [hpre] using hpu.1
  have hv' : MemW12 (Ω b c) pv pDv := by simpa only [hpre] using hpv.1
  have hEu : (∫ x in (Ω a b).val, hsNormSq (pDu x)) =
      ∫ x in (R a b).val, hsNormSq (Du x) := by simpa only [hset] using hpu.2.2.1
  have hEv : (∫ x in (Ω b c).val, hsNormSq (pDv x)) =
      ∫ x in (R b c).val, hsNormSq (Dv x) := by simpa only [hset] using hpv.2.2.1
  let pf : Domain (n + 1) → Ambient q := fun x => if T x < b then pu x else pv x
  let pDf : Domain (n + 1) → Gradient (n + 1) q :=
    fun x i => if T x < b then pDu x i else pDv x i
  have hglue := memW12_coordinate_piecewise_of_common_raw_L2_limit (n := n) (q := q)
    U (a := a) (b := b) (c := c) hab hbc pu pv pDu pDv hu' hv' g hg hleft hright
  have hpW : MemW12 (Ω a c) pf pDf := hglue.1
  have hpE : (∫ x in (Ω a c).val, hsNormSq (pDf x)) =
      (∫ x in (Ω a b).val, hsNormSq (pDu x)) +
      (∫ x in (Ω b c).val, hsNormSq (pDv x)) := hglue.2.1
  have hback := memW12_isometric_preimage_energy (hfinite a c) hpW Q.symm
  have hf : pf ∘ Q.symm = f := by
    funext x
    simp only [Function.comp_apply, pf, pu, pv, f, Q.apply_symm_apply]
  have hD : (fun x i => ∑ j : Fin (n + 1), (Q.symm (EuclideanSpace.single i 1)) j •
      pDf (Q.symm x) j) = Df := by
    funext x i
    dsimp only [pDf, pDu, pDv, Df]
    by_cases ht : T (Q.symm x) < b
    · simp only [ht, if_true, Q.apply_symm_apply]
      exact source_isometry_inverse_columns Q (Du x) i
    · simp only [ht, if_false, Q.apply_symm_apply]
      exact source_isometry_inverse_columns Q (Dv x) i
  have hW : MemW12 (R a c) f Df := by
    have hh := hback.1
    change MemW12 (R a c) (pf ∘ Q.symm)
      (fun x i => ∑ j : Fin (n + 1), (Q.symm (EuclideanSpace.single i 1)) j • pDf (Q.symm x) j) at hh
    rw [hf, hD] at hh
    exact hh
  have hEback : (∫ y in (R a c).val, hsNormSq (Df y)) =
      ∫ x in (Ω a c).val, hsNormSq (pDf x) := by
    have hh := hback.2.2.1
    change (∫ x in (R a c).val, hsNormSq ((fun x i => ∑ j : Fin (n + 1),
      (Q.symm (EuclideanSpace.single i 1)) j • pDf (Q.symm x) j) x)) = _ at hh
    rw [hD] at hh
    exact hh
  refine ⟨hW, ?_, ?_⟩
  · rw [hEback, hpE, hEu, hEv]
  · obtain ⟨J, hJ, hJb⟩ := hglue.2.2
    refine ⟨J, ?_, hJb⟩
    simpa only [pf, pu, pv, f, Function.comp_apply, Q.symm_apply_apply] using hJ

end StratificationTheory
