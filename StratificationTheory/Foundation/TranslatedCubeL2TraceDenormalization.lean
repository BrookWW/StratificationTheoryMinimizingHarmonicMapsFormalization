module

public import StratificationTheory.Foundation.TranslatedCubeAffineCoordinates
public import StratificationTheory.Foundation.ShiftedIntervalL2Trace
public import StratificationTheory.Foundation.SurfaceL2TraceTransport

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- The actual inverse spatial similarity and inverse time normalization
transport a full unit-face trace to its full translated physical face. Both
original endpoint classes and the original raw slices are retained. -/
theorem exists_translated_cube_L2_trace_denormalization {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {ε : ℝ} (hε : 0 < ε)
    (lo : Domain n) (t₀ : ℝ) (f : Domain n × ℝ → E) (g₀ g₁ : Domain n → E) :
    let B := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let S := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (lo j) (lo j + ε)
    let a : Domain n := lo + WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain n → Domain n := fun y => (ε / 2)⁻¹ • (y - a)
    ∀ H : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => f (x, t)) 2 (volume.restrict B),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (x, t))) →
    ((H ⟨-1, le_rfl, by norm_num⟩ : Domain n → E) =ᵐ[volume.restrict B] g₀) →
    ((H ⟨1, by norm_num, le_rfl⟩ : Domain n → E) =ᵐ[volume.restrict B] g₁) →
    ∃ K : C(Icc t₀ (t₀ + ε), Lp E 2 (volume.restrict S)),
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo t₀ (t₀ + ε),
        ∃ hs : MemLp (fun x => f (F x, (r - t₀) / (ε / 2) - 1)) 2 (volume.restrict S),
          K ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => f (F x, (r - t₀) / (ε / 2) - 1))) ∧
      ((K ⟨t₀, le_rfl, by linarith⟩ : Domain n → E) =ᵐ[volume.restrict S] (g₀ ∘ F)) ∧
      ((K ⟨t₀ + ε, by linarith, le_rfl⟩ : Domain n → E) =ᵐ[volume.restrict S] (g₁ ∘ F)) ∧
      ∀ J : C(Icc t₀ (t₀ + ε), Lp E 2 (volume.restrict S)),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo t₀ (t₀ + ε),
          ∃ hs : MemLp (fun x => f (F x, (r - t₀) / (ε / 2) - 1)) 2 (volume.restrict S),
            J ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => f (F x, (r - t₀) / (ε / 2) - 1))) → J = K := by
  intro B S a F H hH hEnd₀ hEnd₁
  let FH : Domain n ≃ₜ Domain n :=
    (Homeomorph.addRight (-a)).trans (Homeomorph.smul (Units.mk0 (ε / 2)⁻¹ (inv_ne_zero (half_pos hε).ne')))
  have hFH : (FH : Domain n → Domain n) = F := by
    funext x
    change (ε / 2)⁻¹ • (x + -a) = (ε / 2)⁻¹ • (x - a)
    rw [sub_eq_add_neg]
  have hmap : Measure.map FH (volume.restrict S) ≤
      ENNReal.ofReal ((ε / 2) ^ n) • volume.restrict B := by
    rw [hFH]
    exact le_of_eq (map_inverse_translated_cube_volume n hε lo)
  have hQ : Measure.QuasiMeasurePreserving FH (volume.restrict S) (volume.restrict B) :=
    ⟨FH.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  obtain ⟨J, hJall, hJpull, _hJUnique⟩ :=
    exists_continuous_L2_curve_homeomorph_pullback FH ENNReal.ofReal_ne_top hmap H
  have hJ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => f (F x, t)) 2 (volume.restrict S),
        J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (F x, t)) := by
    filter_upwards [hH] with t ht htI
    obtain ⟨hs, hClass⟩ := ht htI
    simpa only [hFH, Function.comp_def] using hJpull ⟨t, htI.1.le, htI.2.le⟩ (fun x => f (x, t)) hs hClass
  have hJEnd (r : Icc (-1 : ℝ) 1) (g : Domain n → E)
      (hEnd : (H r : Domain n → E) =ᵐ[volume.restrict B] g) :
      (J r : Domain n → E) =ᵐ[volume.restrict S] (g ∘ F) := by
    obtain ⟨hs, hClass⟩ := hJall r
    rw [hClass]
    simpa only [hFH, Function.comp_def] using hs.coeFn_toLp.trans (hQ.ae hEnd)
  obtain ⟨K, hK, hK₀, hK₁⟩ :=
    exists_shifted_segment_L2_trace_of_unit_interval hε t₀ (fun z => f (F z.1, z.2)) J hJ
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · rw [hK₀]
    exact hJEnd _ _ hEnd₀
  · rw [hK₁]
    exact hJEnd _ _ hEnd₁
  · intro L hL
    exact continuous_Lp_representatives_eq_of_ae_slices
      (f := fun z : Domain n × ℝ => f (F z.1, (z.2 - t₀) / (ε / 2) - 1))
      (g := fun z : Domain n × ℝ => f (F z.1, (z.2 - t₀) / (ε / 2) - 1))
      (by linarith : t₀ < t₀ + ε) L K hL hK (Eventually.of_forall fun _ _ => EventuallyEq.rfl)

end StratificationTheory
