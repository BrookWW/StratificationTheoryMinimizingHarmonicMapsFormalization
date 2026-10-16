module

public import StratificationTheory.Foundation.CubicalFaceSobolevQualification
public import StratificationTheory.Foundation.CubicalFaceSampling

/-!
# Exact native parameterization of sampled coordinate faces

The scalar sampler's ordinary coordinate kernel is the same translated
native Euclidean face map. Restricted native measure, arbitrary raw
almost-everywhere properties and nonnegative integrals agree exactly.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The physical translated native face map equals the sampler's original
coordinate-kernel formula, with no change to its origin or parameters. -/
theorem translated_coordinate_face_eq_toLp {N k : ℕ}
    (face : Fin k ↪ Fin N) (y : Fin N → ℝ) (t : Fin k → ℝ) :
    WithLp.toLp 2 y +
      ∑ j : Fin k, (WithLp.toLp 2 t : Domain k) j •
        EuclideanSpace.single (face j) (1 : ℝ) =
      WithLp.toLp 2 (y + fun l : Fin N => ∑ j : Fin k, if face j = l then t j else 0) := by
  rw [coordinate_face_embedding_sum_eq_toLp]
  rfl

/-- Native and ordinary coordinate half-open parameter cubes carry the same
restricted measure under the actual Euclidean `toLp` map. -/
theorem measurePreserving_toLp_halfOpen_cube (k : ℕ) (ε : ℝ) :
    let C : Set (Domain k) :=
      ⋂ j : Fin k, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε
    let B : Set (Fin k → ℝ) := Set.univ.pi (fun _ : Fin k => Ico (0 : ℝ) ε)
    MeasurePreserving (WithLp.toLp 2 : (Fin k → ℝ) → Domain k)
      (volume.restrict B) (volume.restrict C) := by
  intro C B
  have hC : MeasurableSet C := MeasurableSet.iInter fun j : Fin k =>
    measurableSet_Ico.preimage (EuclideanSpace.proj j).continuous.measurable
  have hm := (PiLp.volume_preserving_toLp (Fin k)).restrict_preimage hC
  have hpre : (WithLp.toLp 2 : (Fin k → ℝ) → Domain k) ⁻¹' C = B := by
    ext t
    simp only [C, B, mem_preimage, mem_iInter, Set.mem_pi, Set.mem_univ, forall_const]
    rfl
  rwa [hpre] at hm

/-- Arbitrary nonnegative face integrals agree exactly in native Euclidean
and sampler coordinates; no measurability of the integrand is required. -/
theorem lintegral_native_coordinate_face_eq_pi {N k : ℕ}
    (face : Fin k ↪ Fin N) (y : Fin N → ℝ) (ε : ℝ) (f : Domain N → ℝ≥0∞) :
    let C : Set (Domain k) :=
      ⋂ j : Fin k, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε
    let B : Set (Fin k → ℝ) := Set.univ.pi (fun _ : Fin k => Ico (0 : ℝ) ε)
    (∫⁻ t in C, f (WithLp.toLp 2 y +
      ∑ j : Fin k, t j • EuclideanSpace.single (face j) (1 : ℝ))) =
    ∫⁻ t in B,
      f (WithLp.toLp 2 (y + fun l : Fin N => ∑ j : Fin k, if face j = l then t j else 0)) := by
  intro C B
  have h := (measurePreserving_toLp_halfOpen_cube k ε).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding
    (fun t : Domain k => f (WithLp.toLp 2 y +
      ∑ j : Fin k, t j • EuclideanSpace.single (face j) (1 : ℝ)))
  simpa only [translated_coordinate_face_eq_toLp] using h.symm

/-- Raw a.e. qualifications on a sampled coordinate face are exactly the
same qualifications in the actual native Euclidean face parameter. -/
theorem ae_native_coordinate_face_iff_pi {N k : ℕ}
    (face : Fin k ↪ Fin N) (y : Fin N → ℝ) (ε : ℝ) (P : Domain N → Prop) :
    let C : Set (Domain k) :=
      ⋂ j : Fin k, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε
    let B : Set (Fin k → ℝ) := Set.univ.pi (fun _ : Fin k => Ico (0 : ℝ) ε)
    (∀ᵐ t ∂volume.restrict C, P (WithLp.toLp 2 y +
      ∑ j : Fin k, t j • EuclideanSpace.single (face j) (1 : ℝ))) ↔
    ∀ᵐ t ∂volume.restrict B,
      P (WithLp.toLp 2 (y + fun l : Fin N => ∑ j : Fin k, if face j = l then t j else 0)) := by
  intro C B
  have hm := measurePreserving_toLp_halfOpen_cube k ε
  rw [← hm.map_eq]
  have h := (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding.ae_map_iff
    (μ := volume.restrict B)
    (p := fun t : Domain k => P (WithLp.toLp 2 y +
      ∑ j : Fin k, t j • EuclideanSpace.single (face j) (1 : ℝ)))
  simpa only [MeasurableEquiv.coe_toLp, translated_coordinate_face_eq_toLp] using h

end StratificationTheory
