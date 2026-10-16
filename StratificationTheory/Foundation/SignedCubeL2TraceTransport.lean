module

public import StratificationTheory.Foundation.SurfaceL2TraceTransport
public import StratificationTheory.Foundation.CubicalSignedPermutations
public import StratificationTheory.Foundation.CubicalConeGeometry

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- Reflection of the actual time coordinate preserves the original raw
normalization and transports the appropriate original endpoint class. -/
theorem exists_unit_interval_L2_trace_time_reflection {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X)
    (F : X × ℝ → E) (g₀ g₁ : X → E) (positive : Bool)
    (H : C(Icc (-1 : ℝ) 1, Lp E 2 μ))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t)))
    (hEnd₀ : (H ⟨-1, le_rfl, by norm_num⟩ : X → E) =ᵐ[μ] g₀)
    (hEnd₁ : (H ⟨1, by norm_num, le_rfl⟩ : X → E) =ᵐ[μ] g₁) :
    ∃ J : C(Icc (-1 : ℝ) 1, Lp E 2 μ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => F (x, if positive then t else -t)) 2 μ,
          J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, if positive then t else -t))) ∧
      (J ⟨1, by norm_num, le_rfl⟩ : X → E) =ᵐ[μ] (if positive then g₁ else g₀) := by
  cases positive
  · have hτ (t : Icc (-1 : ℝ) 1) : -t.val ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
    let τ : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1) :=
      ⟨fun t => ⟨-t.val, hτ t⟩, continuous_subtype_val.neg.subtype_mk hτ⟩
    let J := H.comp τ
    refine ⟨J, ?_, hEnd₀⟩
    have hPull := ((volume : Measure ℝ).quasiMeasurePreserving_smul (by norm_num : (-1 : ℝ) ≠ 0)).ae hH
    filter_upwards [hPull] with t ht htI
    have hneg : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [htI.2], by linarith [htI.1]⟩
    change ∃ hs : MemLp (fun x => F (x, -t)) 2 μ,
      H ⟨-t, hneg.1.le, hneg.2.le⟩ = hs.toLp (fun x => F (x, -t))
    simpa only [smul_eq_mul, neg_one_mul] using
      ht (by simpa only [smul_eq_mul, neg_one_mul] using hneg)
  · exact ⟨H, hH, hEnd₁⟩

/-- A true finite signed permutation of the native base and a true normal
reflection transport complete original unit-cube trace curves and their
original endpoint classes. -/
theorem exists_signed_cube_L2_trace_transport {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (F : Domain n × ℝ → E) (g₀ g₁ : Domain n → E)
    (p : Equiv.Perm (Fin n)) (s : Fin n → Bool) (positive : Bool) :
    let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let A := cubicalSignedPermutation n p s
    ∀ H : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 (volume.restrict B),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t))) →
    ((H ⟨-1, le_rfl, by norm_num⟩ : Domain n → E) =ᵐ[volume.restrict B] g₀) →
    ((H ⟨1, by norm_num, le_rfl⟩ : Domain n → E) =ᵐ[volume.restrict B] g₁) →
    ∃ J : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => F (A x, if positive then t else -t)) 2 (volume.restrict B),
          J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => F (A x, if positive then t else -t))) ∧
      (J ⟨1, by norm_num, le_rfl⟩ : Domain n → E) =ᵐ[volume.restrict B]
        (fun x => if positive then g₁ (A x) else g₀ (A x)) := by
  intro B A H hH hEnd₀ hEnd₁
  have hB : MeasurableSet B := MeasurableSet.iInter fun k =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable
  have hCube (x : Domain n) : x ∈ B ↔ ‖WithLp.ofLp x‖ < 1 := by
    rw [mem_unit_coordinate_face_iff, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.norm_eq_abs]
  have hPre : A ⁻¹' B = B := by
    ext x
    change A x ∈ B ↔ x ∈ B
    rw [hCube, hCube, cubicalSignedPermutation_coordinate_norm]
  have hMP : MeasurePreserving A (volume.restrict B) (volume.restrict B) := by
    have h := A.measurePreserving.restrict_preimage hB
    rwa [hPre] at h
  have hmap : Measure.map A (volume.restrict B) ≤ (1 : ℝ≥0∞) • volume.restrict B := by
    rw [hMP.map_eq, one_smul]
  obtain ⟨K, hKall, hKpull, _hUnique⟩ :=
    exists_continuous_L2_curve_homeomorph_pullback A.toHomeomorph (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmap H
  have hK : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (A x, t)) 2 (volume.restrict B),
        K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (A x, t)) := by
    filter_upwards [hH] with t ht htI
    obtain ⟨hs, hClass⟩ := ht htI
    exact hKpull _ _ hs hClass
  have hKEnd (r : Icc (-1 : ℝ) 1) (g : Domain n → E)
      (hEnd : (H r : Domain n → E) =ᵐ[volume.restrict B] g) :
      (K r : Domain n → E) =ᵐ[volume.restrict B] (fun x => g (A x)) := by
    obtain ⟨hs, hClass⟩ := hKall r
    rw [hClass]
    exact hs.coeFn_toLp.trans (hMP.quasiMeasurePreserving.ae hEnd)
  have hResult := exists_unit_interval_L2_trace_time_reflection (volume.restrict B)
    (fun z => F (A z.1, z.2)) (fun x => g₀ (A x)) (fun x => g₁ (A x)) positive K hK
      (hKEnd _ _ hEnd₀) (hKEnd _ _ hEnd₁)
  cases positive <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using hResult

end StratificationTheory
