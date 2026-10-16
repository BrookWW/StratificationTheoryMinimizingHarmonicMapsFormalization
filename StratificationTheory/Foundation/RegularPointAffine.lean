module

public import StratificationTheory.Foundation.RegularPointNeighborhoods
public import HarmonicMaps.Analysis.AffineBallMeasure

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StratificationTheory

/-- Positive affine changes of variables preserve a local smooth a.e.
representative on the exact inverse-image domain. -/
theorem isRegularPoint_affine_preimage {n q : ℕ}
    (Ω Ω' : OpenDomain n) (u : Domain n → Ambient q)
    (a : Domain n) (ρ : PositiveRadius)
    (hΩ' : Ω'.val = (fun z => a + ρ.val • z) ⁻¹' Ω.val)
    (b : Ω'.val)
    (hreg : IsRegularPoint Ω u
      ⟨a + ρ.val • b.val, by simpa only [hΩ', mem_preimage] using b.property⟩) :
    IsRegularPoint Ω' (fun z => u (a + ρ.val • z)) b := by
  obtain ⟨r, hr, hball, w, hw, hae⟩ := hreg
  have harg (z : Domain n) :
      (a + ρ.val • b.val) + ρ.val • (z - b.val) = a + ρ.val • z := by
    rw [smul_sub]
    abel
  have hmaps : MapsTo (fun z => a + ρ.val • z)
      (Metric.ball b.val (r / ρ.val)) (Metric.ball (a + ρ.val • b.val) r) := by
    intro z hz
    simpa only [harg z] using
      (affineBall_mem_ball_iff (a + ρ.val • b.val) b.val ρ.property r z).mpr hz
  refine ⟨r / ρ.val, div_pos hr ρ.property, ?_,
    fun z => w (a + ρ.val • z), ?_, ?_⟩
  · intro z hz
    rw [hΩ']
    exact hball (hmaps hz)
  · exact hw.comp (by fun_prop) hmaps
  · have h := ae_affineBall (a + ρ.val • b.val) b.val ρ.property r hae
    change ∀ᵐ z ∂volume.restrict (Metric.ball b.val (r / ρ.val)),
      w (a + ρ.val • z) = u (a + ρ.val • z)
    simpa only [harg] using h

/-- The regular locus transforms exactly under a positive affine coordinate
change, without selecting a global representative. -/
theorem isRegularPoint_affine_preimage_iff {n q : ℕ}
    (Ω Ω' : OpenDomain n) (u : Domain n → Ambient q)
    (a : Domain n) (ρ : PositiveRadius)
    (hΩ' : Ω'.val = (fun z => a + ρ.val • z) ⁻¹' Ω.val)
    (b : Ω'.val) :
    IsRegularPoint Ω' (fun z => u (a + ρ.val • z)) b ↔
      IsRegularPoint Ω u
        ⟨a + ρ.val • b.val, by simpa only [hΩ', mem_preimage] using b.property⟩ := by
  have hb : a + ρ.val • b.val ∈ Ω.val := by
    simpa only [hΩ', mem_preimage] using b.property
  constructor
  · intro hreg
    let σ : PositiveRadius := ⟨ρ.val⁻¹, inv_pos.mpr ρ.property⟩
    let c : Domain n := -(ρ.val⁻¹ • a)
    have hinv (z : Domain n) : c + σ.val • z = ρ.val⁻¹ • (z - a) := by
      dsimp only [c, σ]
      rw [smul_sub]
      abel
    have hforward (z : Domain n) : a + ρ.val • (c + σ.val • z) = z := by
      rw [hinv, smul_smul, mul_inv_cancel₀ ρ.property.ne', one_smul, add_sub_cancel]
    have hback (z : Domain n) : c + σ.val • (a + ρ.val • z) = z := by
      rw [hinv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul]
    have hΩ : Ω.val = (fun z => c + σ.val • z) ⁻¹' Ω'.val := by
      ext z
      rw [hΩ']
      simp only [mem_preimage, hforward]
    have hreg' : IsRegularPoint Ω' (fun z => u (a + ρ.val • z))
        ⟨c + σ.val • (a + ρ.val • b.val), by rw [hback]; exact b.property⟩ := by
      simpa only [hback] using hreg
    have h := isRegularPoint_affine_preimage Ω' Ω (fun z => u (a + ρ.val • z))
      c σ hΩ ⟨a + ρ.val • b.val, hb⟩ hreg'
    simpa only [hforward] using h
  · exact isRegularPoint_affine_preimage Ω Ω' u a ρ hΩ' b

/-- Singularity uses the same transported point and the literal complement
of the regular-point predicate. -/
theorem mem_singularSet_affine_preimage_iff {n q : ℕ}
    (Ω Ω' : OpenDomain n) (u : Domain n → Ambient q)
    (a : Domain n) (ρ : PositiveRadius)
    (hΩ' : Ω'.val = (fun z => a + ρ.val • z) ⁻¹' Ω.val)
    (b : Ω'.val) :
    b ∈ singularSet Ω' (fun z => u (a + ρ.val • z)) ↔
      (⟨a + ρ.val • b.val,
        by simpa only [hΩ', mem_preimage] using b.property⟩ : Ω.val) ∈
        singularSet Ω u :=
  not_congr (isRegularPoint_affine_preimage_iff Ω Ω' u a ρ hΩ' b)

end StratificationTheory
