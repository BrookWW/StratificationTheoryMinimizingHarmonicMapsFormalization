module

public import StratificationTheory.Foundation.AffineDomainSobolevPullback

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory.Compactness

/-- Translation preserves the actual annular Sobolev pair, its native HS
energy and every a.e. value constraint. -/
theorem memW12_annular_translation {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    {a b : ℝ}
    (hu : MemW12 ⟨{x : Domain n | a < ‖x‖ ∧ ‖x‖ < b},
      isOpen_Ioo.preimage continuous_norm⟩ u Du) (c : Domain n) :
    let A : OpenDomain n := ⟨{x : Domain n | a < ‖x - c‖ ∧ ‖x - c‖ < b},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩
    MemW12 A (fun x => u (x - c)) (fun x i => Du (x - c) i) ∧
      (∫ x in A.val, hsNormSq (fun i => Du (x - c) i)) =
        ∫ x in {x : Domain n | a < ‖x‖ ∧ ‖x‖ < b}, hsNormSq (Du x) ∧
      ∀ P : Ambient q → Prop,
        (∀ᵐ x ∂volume.restrict {x : Domain n | a < ‖x‖ ∧ ‖x‖ < b}, P (u x)) →
        ∀ᵐ x ∂volume.restrict A.val, P (u (x - c)) := by
  intro A
  let B : OpenDomain n := ⟨{x : Domain n | a < ‖x‖ ∧ ‖x‖ < b},
    isOpen_Ioo.preimage continuous_norm⟩
  have hsub : B.val ⊆ ball (0 : Domain n) b := fun _ hx =>
    mem_ball_zero_iff.mpr hx.2
  have hfinite : (volume : Measure (Domain n)) B.val ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hsub)
  have h := memW12_affine_preimage_energy hfinite hu (0 : Domain n) c
    (by norm_num : (0 : ℝ) < 1)
  simpa only [A, B, one_smul, zero_add, one_zpow, one_pow, inv_one, one_mul,
    Function.comp_def, preimage_setOf_eq] using And.intro h.1 (And.intro h.2.2.1 h.2.2.2.2)

end StratificationTheory.Compactness
