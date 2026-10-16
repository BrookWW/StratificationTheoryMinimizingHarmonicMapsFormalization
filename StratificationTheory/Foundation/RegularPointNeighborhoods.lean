module

public import StratificationTheory.Frozen.SingularSet
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Regular-point neighborhood carriers

The literal regular-point predicate agrees with smooth a.e. representatives
on open neighborhoods, including representatives defined on the open-domain
subtype. A local smooth function has a total ambient extension whose values
outside the neighborhood are unconstrained. No global representative is chosen
as part of the regular-point definition.
-/

public section

open HarmonicMaps MeasureTheory Filter Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace StratificationTheory

theorem isRegularPoint_iff_exists_open_neighborhood {n q : ℕ}
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (a : Ω.val) :
    IsRegularPoint Ω u a ↔
      ∃ U : OpenDomain n, a.val ∈ U.val ∧ U.val ⊆ Ω.val ∧
        ∃ w : Domain n → Ambient q, ContDiffOn ℝ ∞ w U.val ∧
          w =ᵐ[volume.restrict U.val] u := by
  constructor
  · rintro ⟨r, hr, hball, w, hw, hae⟩
    exact ⟨ballDomain a.val r, Metric.mem_ball_self hr, hball, w, hw, hae⟩
  · rintro ⟨U, haU, hUΩ, w, hw, hae⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.property a.val haU
    exact ⟨r, hr, hball.trans hUΩ, w, hw.mono hball,
      ae_restrict_of_ae_restrict_of_subset hball hae⟩

theorem exists_contDiffOn_extension_of_contMDiff {n q : ℕ}
    (U : Opens (Domain n)) (w : U → Ambient q)
    (hw : ContMDiff 𝓘(ℝ, Domain n) 𝓘(ℝ, Ambient q) ∞ w) :
    ∃ f : Domain n → Ambient q, ContDiffOn ℝ ∞ f U ∧
      ∀ x : U, f x = w x := by
  let f : Domain n → Ambient q := Function.extend Subtype.val w 0
  have hrestrict : (fun x : U => f x) = w := by
    exact Function.extend_comp Subtype.val_injective w 0
  refine ⟨f, ?_, congrFun hrestrict⟩
  apply contMDiffOn_iff_contDiffOn.mp
  intro x hx
  have hsub : ContMDiffAt 𝓘(ℝ, Domain n) 𝓘(ℝ, Ambient q) ∞
      (fun z : U => f z) (⟨x, hx⟩ : U) := by
    rw [hrestrict]
    exact hw.contMDiffAt
  exact (contMDiffAt_subtype_iff.mp hsub).contMDiffWithinAt

theorem isRegularPoint_of_contMDiff_subtype_representative {n q : ℕ}
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (a : Ω.val)
    (U : Opens (Domain n)) (ha : a.val ∈ U) (hU : (U : Set (Domain n)) ⊆ Ω.val)
    (w : U → Ambient q)
    (hw : ContMDiff 𝓘(ℝ, Domain n) 𝓘(ℝ, Ambient q) ∞ w)
    (hae : ∀ᵐ x ∂volume.restrict U, ∀ hx : x ∈ U, w ⟨x, hx⟩ = u x) :
    IsRegularPoint Ω u a := by
  obtain ⟨f, hf, hfw⟩ := exists_contDiffOn_extension_of_contMDiff U w hw
  apply (isRegularPoint_iff_exists_open_neighborhood Ω u a).mpr
  refine ⟨⟨U, U.isOpen⟩, ha, hU, f, hf, ?_⟩
  filter_upwards [hae, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
  exact (hfw ⟨x, hxU⟩).trans (hx hxU)

theorem isRegularPoint_iff_exists_contMDiff_subtype_representative {n q : ℕ}
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (a : Ω.val) :
    IsRegularPoint Ω u a ↔
      ∃ U : Opens (Domain n), a.val ∈ U ∧ (U : Set (Domain n)) ⊆ Ω.val ∧
        ∃ w : U → Ambient q,
          ContMDiff 𝓘(ℝ, Domain n) 𝓘(ℝ, Ambient q) ∞ w ∧
          ∀ᵐ x ∂volume.restrict U, ∀ hx : x ∈ U, w ⟨x, hx⟩ = u x := by
  constructor
  · intro hreg
    obtain ⟨U, ha, hU, f, hf, hae⟩ :=
      (isRegularPoint_iff_exists_open_neighborhood Ω u a).mp hreg
    let V : Opens (Domain n) := ⟨U.val, U.property⟩
    refine ⟨V, ha, hU, fun x => f x.val, ?_, ?_⟩
    · intro x
      apply contMDiffAt_subtype_iff.mpr
      exact ((hf x.val x.property).contDiffAt (U.property.mem_nhds x.property)).contMDiffAt
    · filter_upwards [hae] with x hx
      intro _
      exact hx
  · rintro ⟨U, ha, hU, w, hw, hae⟩
    exact isRegularPoint_of_contMDiff_subtype_representative Ω u a U ha hU w hw hae

theorem IsRegularPoint.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {a : Ω.val}
    (hreg : IsRegularPoint Ω u a) (huv : u =ᵐ[volume.restrict Ω.val] v) :
    IsRegularPoint Ω v a := by
  obtain ⟨r, hr, hball, w, hw, hwu⟩ := hreg
  exact ⟨r, hr, hball, w, hw,
    hwu.trans (ae_restrict_of_ae_restrict_of_subset hball huv)⟩

theorem isRegularPoint_congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} (huv : u =ᵐ[volume.restrict Ω.val] v) (a : Ω.val) :
    IsRegularPoint Ω u a ↔ IsRegularPoint Ω v a :=
  ⟨fun h => h.congr_ae huv, fun h => h.congr_ae huv.symm⟩

theorem singularSet_congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} (huv : u =ᵐ[volume.restrict Ω.val] v) :
    singularSet Ω u = singularSet Ω v := by
  ext a
  exact not_congr (isRegularPoint_congr_ae huv a)

theorem isOpen_regularPoints {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) : IsOpen {a : Ω.val | IsRegularPoint Ω u a} := by
  let A : Set (Domain n) := {x | ∃ hx : x ∈ Ω.val, IsRegularPoint Ω u ⟨x, hx⟩}
  have hA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hxΩ, hx⟩
    obtain ⟨U, hxU, hUΩ, w, hw, hwu⟩ :=
      (isRegularPoint_iff_exists_open_neighborhood Ω u ⟨x, hxΩ⟩).mp hx
    apply mem_of_superset (U.property.mem_nhds hxU)
    intro y hy
    refine ⟨hUΩ hy, ?_⟩
    exact (isRegularPoint_iff_exists_open_neighborhood Ω u ⟨y, hUΩ hy⟩).mpr
      ⟨U, hy, hUΩ, w, hw, hwu⟩
  have heq : {a : Ω.val | IsRegularPoint Ω u a} = Subtype.val ⁻¹' A := by
    ext a
    constructor
    · intro ha
      exact ⟨a.property, ha⟩
    · rintro ⟨hx, ha⟩
      exact ha
  rw [heq]
  exact hA.preimage continuous_subtype_val

theorem isClosed_singularSet {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) : IsClosed (singularSet Ω u) :=
  (isOpen_regularPoints Ω u).isClosed_compl

end StratificationTheory
