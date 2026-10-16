module

public import StratificationTheory.Interpolation.ProjectedAnnularConnector
public import StratificationTheory.Interpolation.CircleCylinderDistance

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff
namespace StratificationTheory.Interpolation

/-- Native circle discrepancy smallness produces the tubular condition and
one actual target-valued thin annular connector with both endpoint traces.
The smooth projection and its admissible discrepancy radius depend only on
the compact embedded target. -/
theorem exists_projected_circle_annulus_of_small_discrepancy {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q),
      0 < ρ ∧ ContDiff ℝ ∞ Q ∧ (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ (s η : ℝ) (hs : 0 < s) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
        (u v : sphere (0 : Domain 2) 1 → Ambient q)
        (hu : MemSphereW12 (Nat.le_refl 2) u) (hv : MemSphereW12 (Nat.le_refl 2) v)
        (huN : ∀ᵐ θ ∂Measure.euclideanHausdorffMeasure 1, u θ ∈ N.carrierSet)
        (hvN : ∀ᵐ θ ∂Measure.euclideanHausdorffMeasure 1, v θ ∈ N.carrierSet),
      let σ : Measure (sphere (0 : Domain 2) 1) := Measure.euclideanHausdorffMeasure 1
      let A := ∫ θ : sphere (0 : Domain 2) 1,
        ∑ i : Fin 2, (‖(sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2 +
          ‖(sphereGradient (Nat.le_refl 2) v hv i) θ‖ ^ 2) ∂σ
      let D := ∫ θ : sphere (0 : Domain 2) 1, ‖v θ - u θ‖ ^ 2 ∂σ
      let lo := s * (1 + -η)
      let V : OpenDomain 2 := ⟨{x : Domain 2 | lo < ‖x‖ ∧ ‖x‖ < s},
        isOpen_Ioo.preimage continuous_norm⟩
      8 * Real.sqrt (A * D) + 8 * D < ρ ^ 2 →
      ∃ W : Domain 2 → Ambient q, ∃ DW : Domain 2 → Gradient 2 q,
        ∃ K : C(Icc lo s, Lp (Ambient q) 2 σ),
          MemW12 V W DW ∧
          (∀ (θ : sphere (0 : Domain 2) 1) (t : ℝ), t ∈ Ioo (-η) 0 →
            W ((s * (1 + t)) • θ.val) =
              Q ((1 - (t + η) / η) • u θ + ((t + η) / η) • v θ)) ∧
          (∀ᵐ x ∂volume.restrict V.val, W x ∈ N.carrierSet) ∧
          (∫ x in V.val, hsNormSq (DW x)) ≤ 8 * η * A + 16 * η⁻¹ * D ∧
          (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo lo s,
            ∃ hslice : MemLp (fun θ : sphere (0 : Domain 2) 1 => W (r • θ.val)) 2 σ,
              K ⟨r, hr.1.le, hr.2.le⟩ =
                hslice.toLp (fun θ : sphere (0 : Domain 2) 1 => W (r • θ.val))) ∧
          K ⟨lo, le_rfl, by dsimp only [lo]; nlinarith only [hs, hη]⟩ = hu.1.toLp u ∧
          K ⟨s, by dsimp only [lo]; nlinarith only [hs, hη], le_rfl⟩ = hv.1.toLp v ∧
          (∀ r : Icc lo s, ∀ᵐ θ ∂σ, K r θ ∈ N.carrierSet) := by
  obtain ⟨ρ, Q, hρ, hQ, hfix, hop⟩ := exists_projected_thin_affine_annulus_operator N
  refine ⟨ρ, Q, hρ, hQ, hfix, ?_⟩
  intro s η hs hη hηhalf u v hu hv huN hvN σ A D lo V hsmall
  have hab : -η < (0 : ℝ) := by linarith only [hη]
  have hdist := circle_affine_cylinder_distance_bound hab u v hu hv N.carrierSet (Or.inl huN)
  have hD : (∫ θ : sphere (0 : Domain 2) 1, ‖u θ - v θ‖ ^ 2 ∂σ) = D := by
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => congrArg (fun z : ℝ => z ^ 2) (norm_sub_rev (u θ) (v θ))
  change ∀ᵐ y : unitCylinder 2 (-η) 0 ∂Measure.euclideanHausdorffMeasure 2,
    (infDist ((1 - (((EuclideanSpace.finAddEquivProd y.val).2 0) - -η) / (0 - -η)) •
      u ⟨(EuclideanSpace.finAddEquivProd y.val).1, y.property.1⟩ +
      ((((EuclideanSpace.finAddEquivProd y.val).2 0) - -η) / (0 - -η)) •
      v ⟨(EuclideanSpace.finAddEquivProd y.val).1, y.property.1⟩) N.carrierSet) ^ 2 ≤
        8 * Real.sqrt (A * (∫ θ : sphere (0 : Domain 2) 1, ‖u θ - v θ‖ ^ 2 ∂σ)) +
          8 * (∫ θ : sphere (0 : Domain 2) 1, ‖u θ - v θ‖ ^ 2 ∂σ) at hdist
  rw [hD] at hdist
  simp only [sub_neg_eq_add, zero_add] at hdist
  have htube : ∀ᵐ y : unitCylinder 2 (-η) 0 ∂Measure.euclideanHausdorffMeasure 2,
      infDist ((1 - (((EuclideanSpace.finAddEquivProd y.val).2 0) + η) / η) •
        u ⟨(EuclideanSpace.finAddEquivProd y.val).1, y.property.1⟩ +
        ((((EuclideanSpace.finAddEquivProd y.val).2 0) + η) / η) •
        v ⟨(EuclideanSpace.finAddEquivProd y.val).1, y.property.1⟩) N.carrierSet < ρ := by
    filter_upwards [hdist] with y hy
    have hsq := hy.trans_lt hsmall
    nlinarith only [hsq, hρ]
  obtain ⟨W, DW, K, hW, hraw, hN, hE, hT, hTa, hTb, hTN⟩ :=
    hop 2 (Nat.le_refl 2) s η hs hη hηhalf u v hu hv huN hvN htube
  refine ⟨W, DW, K, hW, hraw, hN, ?_, hT, hTa, hTb, hTN⟩
  calc
    _ ≤ 16 * s ^ (2 - 2) * ((η / 2) * A + η⁻¹ * D) := hE
    _ = _ := by norm_num only [Nat.sub_self, pow_zero, mul_one]; ring

end StratificationTheory.Interpolation
