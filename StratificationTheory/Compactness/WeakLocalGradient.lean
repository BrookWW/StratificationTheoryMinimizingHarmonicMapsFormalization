module

public import StratificationTheory.Compactness.LocalRellichCompact
public import StratificationTheory.Compactness.CountableWeakHilbert
public import StratificationTheory.Compactness.CofinalCompactExhaustion
public import StratificationTheory.Compactness.AELocalGluing
public import StratificationTheory.Compactness.WeakL2Localization
public import StratificationTheory.Compactness.EnergyColumnBounds
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace StratificationTheory.Compactness

/-- Local HS energy bounds on an actual displayed field admit one subsequence
and one global field with weak L2 convergence of every column on every compact
region. The field's local L2 data and overlap consistency are produced. -/
theorem exists_weak_local_gradient_subsequence {n q : ℕ}
    (Ω : OpenDomain n) (Du : ℕ → Domain n → Gradient n q)
    (hDu : ∀ k (i : Fin n), LocallyMemL2 Ω (fun x => Du k x i))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ (∀ i : Fin n, LocallyMemL2 Ω (fun x => Dv x i)) ∧
      ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
          Tendsto (fun k => ∫ x in K, inner ℝ (Du (κ k) x i) (w x))
            atTop (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x))) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨K, hK, hKΩ, hKmono, _hcover, hcofinal⟩ := exists_cofinal_compact_exhaustion_openDomain Ω
  have hC (j : ℕ) := local_energy_bound_on_compact Ω Du hEnergy (K j) (hK j) (hKΩ j)
  choose C hC using hC
  have hCols (j k : ℕ) (i : Fin n) : MemLp (fun x => Du k x i) 2 (volume.restrict (K j)) :=
    hDu k i (K j) (hK j) (hKΩ j)
  letI (j : ℕ) : IsFiniteMeasure (volume.restrict (K j)) :=
    isFiniteMeasure_restrict.mpr (hK j).measure_lt_top.ne
  let H (j : ℕ) : Type := PiLp 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict (K j)))
  letI (j : ℕ) : SecondCountableTopology (Lp (Ambient q) 2 (volume.restrict (K j))) :=
    Lp.SecondCountableTopology
  letI (j : ℕ) : SecondCountableTopology (H j) := by
    dsimp only [H]
    exact PiLp.secondCountableTopology 2 (fun _ : Fin n => Lp (Ambient q) 2 (volume.restrict (K j)))
  letI (j : ℕ) : TopologicalSpace.SeparableSpace (H j) := inferInstance
  let F (k j : ℕ) : H j := WithLp.toLp 2 (fun i => (hCols j k i).toLp (fun x => Du k x i))
  have hnorm (k j : ℕ) : ‖F k j‖ ^ 2 = (dirichletEnergy (Du k) (K j)).toReal := by
    rw [PiLp.norm_sq_eq_of_L2]
    dsimp only [F, H, PiLp.toLp_apply]
    simp only [Lp.norm_toLp]
    exact sum_column_L2_norm_sq_eq_dirichletEnergy (hCols j k)
  have hbound (k j : ℕ) : ‖F k j‖ ≤ Real.sqrt (C j) := by
    apply Real.le_sqrt_of_sq_le
    rw [hnorm]
    have ht := ENNReal.toReal_mono (by simp : (C j : ℝ≥0∞) ≠ ⊤) (hC j k)
    simpa only [ENNReal.coe_toReal] using ht
  obtain ⟨κ, G, hκ, _hG, hweak⟩ := exists_weak_subsequence_countable_hilbert F
    (fun j => Real.sqrt (C j)) hbound
  let D (j : ℕ) : Domain n → Gradient n q := fun x i => G j i x
  have hD (j : ℕ) (i : Fin n) : MemLp (fun x => D j x i) 2 (volume.restrict (K j)) := Lp.memLp (G j i)
  have hweakCols (j : ℕ) (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict (K j))) :
      Tendsto (fun k => ∫ x in K j, inner ℝ (Du (κ k) x i) (w x)) atTop
        (𝓝 (∫ x in K j, inner ℝ (D j x i) (w x))) := by
    have hsingle (v : H j) : inner ℝ v (PiLp.single 2 i w) = inner ℝ (v i) w := by
      simp [H, PiLp.inner_apply, PiLp.single_apply, apply_ite]
    have hp := hweak j (PiLp.single 2 i w)
    simp only [hsingle] at hp
    have heq (k : ℕ) : inner ℝ ((hCols j (κ k) i).toLp (fun x => Du (κ k) x i)) w =
        ∫ x in K j, inner ℝ (Du (κ k) x i) (w x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hCols j (κ k) i).coeFn_toLp] with x hx
      rw [hx]
    simpa only [F, PiLp.toLp_apply, heq, L2.inner_def, D] using hp
  have hconsistent (j l : ℕ) (hjl : j ≤ l) : D j =ᵐ[volume.restrict (K j)] D l := by
    have hcols (i : Fin n) : (fun x => D j x i) =ᵐ[volume.restrict (K j)] (fun x => D l x i) :=
      ae_eq_of_weak_L2_limits (hD j i)
        ((hD l i).mono_measure (Measure.restrict_mono_set volume (hKmono hjl)))
        (hweakCols j i)
        (weak_L2_integral_convergence_mono (hK j).measurableSet (hKmono hjl) (hweakCols l i))
    filter_upwards [ae_all_iff.mpr hcols] with x hx
    exact funext hx
  obtain ⟨Dv, hDvEq⟩ := exists_ae_glue_countable_regions volume K (fun j => (hK j).measurableSet) D hconsistent
  have hDvK (j : ℕ) (i : Fin n) : MemLp (fun x => Dv x i) 2 (volume.restrict (K j)) :=
    (hD j i).ae_eq ((hDvEq j).symm.mono fun x hx => congrFun hx i)
  have hDv (i : Fin n) : LocallyMemL2 Ω (fun x => Dv x i) := by
    intro T hT hTΩ
    obtain ⟨j, hj⟩ := hcofinal T hT hTΩ
    exact (hDvK j i).mono_measure (Measure.restrict_mono_set volume hj)
  refine ⟨κ, Dv, hκ, hDv, ?_⟩
  intro T hT hTΩ i w
  obtain ⟨j, hj⟩ := hcofinal T hT hTΩ
  have hstage (v : Lp (Ambient q) 2 (volume.restrict (K j))) :
      Tendsto (fun k => ∫ x in K j, inner ℝ (Du (κ k) x i) (v x)) atTop
        (𝓝 (∫ x in K j, inner ℝ (Dv x i) (v x))) := by
    have heq : (∫ x in K j, inner ℝ (D j x i) (v x)) =
        ∫ x in K j, inner ℝ (Dv x i) (v x) := by
      apply integral_congr_ae
      filter_upwards [(hDvEq j).symm] with x hx
      rw [hx]
    rw [← heq]
    exact hweakCols j i v
  exact weak_L2_integral_convergence_mono hT.measurableSet hj hstage w

end StratificationTheory.Compactness
