module

public import StratificationTheory.Frozen.CylinderSobolev
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.SobolevRestriction

/-!
# Linear operations on full cylinder Sobolev maps

Scalar multiplication and subtraction preserve the literal finite cylinder
Sobolev predicate. The constructions retain all weak columns and every raw
positive-ray identity; two input neighborhoods are restricted to their
common intersection.
-/

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- Constant scalar multiplication preserves the actual finite weak map and
scales every displayed derivative column by the same scalar. -/
theorem memW12_const_smul {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (c : ℝ) (hu : MemW12 Ω u Du) :
    MemW12 Ω (fun x => c • u x) (fun x i => c • Du x i) := by
  refine ⟨⟨hu.1.1.smul c, fun i => (hu.1.2.1 i).smul c, ?_⟩,
    hu.2.1.const_smul c, fun i => (hu.2.2 i).const_smul c⟩
  intro i φ hφ hc hs
  simp_rw [smul_comm _ c]
  rw [integral_smul, integral_smul, hu.1.2.2 i φ hφ hc hs, smul_neg]

/-- Constant scalar multiplication preserves native L2 and the same complete
radial weak extension of a cylinder map. -/
theorem memCylinderW12_const_smul {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) {v : unitCylinder n a b → Ambient q}
    (c : ℝ) (hv : MemCylinderW12 hn hab v) :
    MemCylinderW12 hn hab (fun y => c • v y) := by
  obtain ⟨hL, U, hS, h0, w, Dw, hW, hraw⟩ := hv
  refine ⟨hL.const_smul c, U, hS, h0, (fun x => c • w x),
    (fun x i => c • Dw x i), memW12_const_smul c hW, ?_⟩
  intro ρ y ht hx
  change c • w _ = c • v y
  rw [hraw ρ y ht hx]

/-- Two full cylinder Sobolev maps subtract on a common spatial neighborhood,
with the difference of their actual full weak-gradient columns. -/
theorem memCylinderW12_sub {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) {u v : unitCylinder n a b → Ambient q}
    (hu : MemCylinderW12 hn hab u) (hv : MemCylinderW12 hn hab v) :
    MemCylinderW12 hn hab (u - v) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  obtain ⟨huL, U, hUS, hU0, f, Df, hf, hfu⟩ := hu
  obtain ⟨hvL, V, hVS, _hV0, g, Dg, hg, hgv⟩ := hv
  let W : OpenDomain n := ⟨U.val ∩ V.val, U.property.inter V.property⟩
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ W.val ∧ (e y).2 0 ∈ Ioo a b},
      (W.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hsubU : Ω.val ⊆ {y : Domain (n + 1) |
      (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b} :=
    fun _ hy => ⟨hy.1.1, hy.2⟩
  have hsubV : Ω.val ⊆ {y : Domain (n + 1) |
      (e y).1 ∈ V.val ∧ (e y).2 0 ∈ Ioo a b} :=
    fun _ hy => ⟨hy.1.2, hy.2⟩
  have hfW : MemW12 Ω f Df :=
    ⟨hf.1.mono hsubU, hf.2.1.mono_measure (Measure.restrict_mono_set volume hsubU),
      fun i => (hf.2.2 i).mono_measure (Measure.restrict_mono_set volume hsubU)⟩
  have hgW : MemW12 Ω g Dg :=
    ⟨hg.1.mono hsubV, hg.2.1.mono_measure (Measure.restrict_mono_set volume hsubV),
      fun i => (hg.2.2 i).mono_measure (Measure.restrict_mono_set volume hsubV)⟩
  refine ⟨huL.sub hvL, W, (fun θ hθ => ⟨hUS hθ, hVS hθ⟩),
    (fun h0 => hU0 h0.1), f - g, (fun x i => Df x i - Dg x i), hfW.sub hgW, ?_⟩
  intro ρ y ht hx
  change f _ - g _ = u y - v y
  rw [hfu ρ y ht hx.1, hgv ρ y ht hx.2]

/-- Addition preserves the complete literal cylinder Sobolev predicate. -/
theorem memCylinderW12_add {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) {u v : unitCylinder n a b → Ambient q}
    (hu : MemCylinderW12 hn hab u) (hv : MemCylinderW12 hn hab v) :
    MemCylinderW12 hn hab (u + v) := by
  have hneg := memCylinderW12_const_smul hn hab (-1) hv
  have hsub := memCylinderW12_sub hn hab hu hneg
  have heq : u - (fun y => (-1 : ℝ) • v y) = u + v := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, neg_one_smul, sub_neg_eq_add]
  rwa [heq] at hsub

end StratificationTheory
