module

public import StratificationTheory.Interpolation.CircleLuckhausJoint
public import StratificationTheory.Interpolation.LuckhausJointHighDimensional

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory.Providers.LuckhausJoint

theorem result (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (N : Set (Ambient q)), IsCompact N →
      ∀ (u v : sphere (0 : Domain n) 1 → Ambient q)
        (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v),
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), u θ ∈ N) →
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), v θ ∈ N) →
      ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) (1 / 8)),
      let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
      let A : ℝ := ∫ θ : sphere (0 : Domain n) 1,
        hsNormSq (fun i : Fin n => (sphereGradient hn u hu i) θ) +
          hsNormSq (fun i : Fin n => (sphereGradient hn v hv i) θ) ∂σ
      let D : ℝ := ∫ θ : sphere (0 : Domain n) 1, ‖u θ - v θ‖ ^ 2 ∂σ
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let μ : Measure (unitCylinder n 0 ε) := Measure.euclideanHausdorffMeasure n
      let U : OpenDomain (n + 1) :=
        ⟨{y | ‖(e y).1‖ ∈ Ioo (1 / 2 : ℝ) 2 ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
          (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ (w : unitCylinder n 0 ε → Ambient q) (hw : MemCylinderW12 hn hε.1 w)
        (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q)
        (g : unitCylinder n 0 ε → Gradient (n + 1) q),
        MemW12 U W DW ∧
        (∀ (r : ℝ), r ∈ Ioo (1 / 2 : ℝ) 2 → ∀ c : unitCylinder n 0 ε,
          (e c.val).2 0 ∈ Ioo (0 : ℝ) ε →
            W (e.symm (r • (e c.val).1, (e c.val).2)) = w c) ∧
        (∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
          ∀ᵐ c : unitCylinder n 0 ε ∂μ, (e c.val).2 0 ∈ Ioo (0 : ℝ) ε →
            (∀ i : Fin n,
              DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
                r⁻¹ • g c (Fin.castAdd 1 i)) ∧
            DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
              g c (Fin.natAdd n (0 : Fin 1))) ∧
        (∀ i : Fin (n + 1), MemLp (fun c : unitCylinder n 0 ε => g c i) 2 μ) ∧
        (∀ᵐ c : unitCylinder n 0 ε ∂μ,
          (∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i)) = 0) ∧
        Integrable (fun c : unitCylinder n 0 ε => hsNormSq (g c)) μ ∧
        (∫ c : unitCylinder n 0 ε, hsNormSq (g c) ∂μ) ≤ C * ε * A + C / ε * D ∧
        (∀ᵐ c : unitCylinder n 0 ε ∂μ,
          (infDist (w c) N) ^ 2 ≤
            C * ε ^ (1 - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
              C * ε ^ (-(n : ℤ)) * D) ∧
        cylinderTrace hn hε.1 w hw ⟨0, le_rfl, hε.1.le⟩ = hu.1.toLp u ∧
        cylinderTrace hn hε.1 w hw ⟨ε, hε.1.le, le_rfl⟩ = hv.1.toLp v :=
by
  by_cases h : n = 2
  · subst n
    exact StratificationTheory.luckhaus_joint_twoDimensional
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
    subst n
    exact StratificationTheory.luckhaus_joint_high_dimensional k

end StratificationTheory.Providers.LuckhausJoint
