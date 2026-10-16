module

public import StratificationTheory.Interpolation.CubicalEdgeInterpolation
public import StratificationTheory.Interpolation.CubicalEdgeNativeTraces
public import StratificationTheory.Foundation.UnitCubeFaceL2Trace

/-!
# The actual unit-face connector of a Sobolev edge pair

One original closed-line pair produces the same unit-square weak map,
energy and target-distance bounds, and all four original native flat
boundary traces. Its spatial boundary edges are the original vertex chords.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

private theorem two_cube_eq_rectangle (a b : ℝ) :
    (⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo a b) =
      {x : Domain 2 | x 0 ∈ Ioo a b ∧ x 1 ∈ Ioo a b} := by
  ext x
  simp only [mem_iInter, mem_preimage, mem_setOf_eq]
  change (∀ j : Fin 2, x j ∈ Ioo a b) ↔ x 0 ∈ Ioo a b ∧ x 1 ∈ Ioo a b
  constructor
  · exact fun h => ⟨h 0, h 1⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2

private theorem affine_unit_square_split_first (ε : ℝ) (x : Domain 1) (s : ℝ) :
    let a : Domain 1 := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    A + (ε / 2) • e.symm (EuclideanSpace.single (0 : Fin 1) s, x) =
      e.symm (EuclideanSpace.single (0 : Fin 1) ((ε / 2) * (s + 1)),
        a + (ε / 2) • x) := by
  intro a A e
  have hA : e A = (EuclideanSpace.single (0 : Fin 1) (ε / 2), a) := by
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  apply e.injective
  rw [map_add, map_smul, e.apply_symm_apply, hA, e.apply_symm_apply]
  apply Prod.ext
  · ext j
    fin_cases j
    change ε / 2 + (ε / 2) * s = (ε / 2) * (s + 1)
    ring
  · rfl

/-- The original finite line data produce one genuine unit-square
connector. The weak graph, quantitative bounds and all four native traces
refer to the same displayed affine map. No boundary Sobolev map or trace
qualification of the connector is an input. -/
theorem exists_unit_affine_edge_connector {q : ℕ} {ε : ℝ} (hε : 0 < ε)
    {F G f h g k : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hh : MemLp h 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hk : MemLp k 2 (volume.restrict (Ioo (0 : ℝ) ε)))
    (hFAC : AbsolutelyContinuousOnInterval F 0 ε)
    (hGAC : AbsolutelyContinuousOnInterval G 0 ε)
    (hFae : F =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] h)
    (hFinc : ∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
      G t - G s = ∫ y in s..t, k y)
    {N : Set (Ambient q)} (hN : IsClosed N)
    (hfN : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ε), f s ∈ N)
    (hhN : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ε), h s ∈ N) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let a : Domain 1 := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun y : Domain 2 => A + (ε / 2) • y
    let L := fun x : Domain 1 => a + (ε / 2) • x
    let W : Domain 2 → Ambient q := fun y =>
      (1 - (e y).2 0 / ε) • F ((e y).1 0) + ((e y).2 0 / ε) • G ((e y).1 0)
    let DW : Domain 2 → Gradient 2 q := fun y =>
      Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - (e y).2 0 / ε) • g ((e y).1 0) +
          ((e y).2 0 / ε) • k ((e y).1 0))
        (fun _ : Fin 1 => ε⁻¹ • (G ((e y).1 0) - F ((e y).1 0)))
    let V := W ∘ T
    let DV := fun y j => (ε / 2) • DW (T y) j
    let chord : ℝ → Domain 1 → Ambient q := fun s x =>
      (1 - x 0 / ε) • F s + (x 0 / ε) • G s
    let D := ∫ s in Ioo (0 : ℝ) ε, ‖f s - h s‖ ^ 2
    let E := ∫ s in Ioo (0 : ℝ) ε, ‖g s‖ ^ 2 + ‖k s‖ ^ 2
    MemW12 B V DV ∧
      (∫ y in B.val, hsNormSq (DV y)) ≤
        (ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖g s‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖k s‖ ^ 2) + ε⁻¹ * D ∧
      (∀ y : Domain 2, (∀ j, y j ∈ Icc (-1 : ℝ) 1) →
        (infDist (V y) N) ^ 2 ≤ D / ε + Real.sqrt (2 * D * E)) ∧
      ∃ HT : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        ∃ HS : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
            2 (volume.restrict C), HT ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp
              (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∃ h₀ : MemLp ((fun x : Domain 1 => f (x 0)) ∘ L) 2 (volume.restrict C),
          HT ⟨-1, le_rfl, by norm_num⟩ = h₀.toLp ((fun x : Domain 1 => f (x 0)) ∘ L)) ∧
        (∃ h₁ : MemLp ((fun x : Domain 1 => h (x 0)) ∘ L) 2 (volume.restrict C),
          HT ⟨1, by norm_num, le_rfl⟩ = h₁.toLp ((fun x : Domain 1 => h (x 0)) ∘ L)) ∧
        (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (e.symm (EuclideanSpace.single (0 : Fin 1) s, x)))
            2 (volume.restrict C), HS ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp
              (fun x => V (e.symm (EuclideanSpace.single (0 : Fin 1) s, x)))) ∧
        (∃ h₀ : MemLp (chord 0 ∘ L) 2 (volume.restrict C),
          HS ⟨-1, le_rfl, by norm_num⟩ = h₀.toLp (chord 0 ∘ L)) ∧
        (∃ h₁ : MemLp (chord ε ∘ L) 2 (volume.restrict C),
          HS ⟨1, by norm_num, le_rfl⟩ = h₁.toLp (chord ε ∘ L)) := by
  intro e B C a A T L W DW V DV chord D E
  let Ω : OpenDomain 2 :=
    ⟨{y : Domain 2 | y 0 ∈ Ioo (0 : ℝ) ε ∧ y 1 ∈ Ioo (0 : ℝ) ε},
      (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
        (isOpen_Ioo.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous)⟩
  have hbase := interval_pair_rectangle_interpolation hε hε hf hh hg hk
    hFAC hGAC hFae hGae hFinc hGinc hN hfN hhN
  dsimp only at hbase
  simp only [sub_zero] at hbase
  have hw : MemW12 Ω W DW := hbase.1
  have henergy : (∫ y in Ω.val, hsNormSq (DW y)) ≤
      (ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖g s‖ ^ 2) +
        ∫ s in Ioo (0 : ℝ) ε, ‖k s‖ ^ 2) + ε⁻¹ * D := hbase.2.2.1
  have hclosed : ∀ y : Domain 2, y 0 ∈ Icc (0 : ℝ) ε → y 1 ∈ Icc (0 : ℝ) ε →
      (infDist (W y) N) ^ 2 ≤ D / ε + Real.sqrt (2 * D * E) := by
    intro y hy₀ hy₁
    exact (hbase.2.2.2.2.2.2.2.1 y hy₀ hy₁).2.2.2
  have hΩ : (⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
      isOpen_iInter_of_finite (fun j : Fin 2 =>
        isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩ : OpenDomain 2) = Ω :=
    Subtype.ext (two_cube_eq_rectangle 0 ε)
  have hwcube : MemW12
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩ W DW := by
    rwa [hΩ]
  obtain ⟨HT, HS, hTrows, ⟨hleft, hT₀⟩, ⟨hright, hT₁⟩,
      hSrows, ⟨hc₀, hS₀⟩, ⟨hc₁, hS₁⟩, _hTU, _hSU⟩ :=
    affine_edge_rectangle_native_four_traces hε hf hh hg hk hFae hGae hFinc hGinc
  obtain ⟨hV, hVE, KT, hKT, hKT₀, hKT₁⟩ :=
    unit_cube_face_sobolev_and_trace (n := 1) hε hwcube HT
      (Eventually.of_forall fun t ht => hTrows ⟨t, ht.1.le, ht.2.le⟩)
      (fun x : Domain 1 => f (x 0)) (fun x : Domain 1 => h (x 0)) hleft hright hT₀ hT₁
  let rawS : Domain 1 × ℝ → Ambient q := fun p =>
    W (e.symm (EuclideanSpace.single (0 : Fin 1) p.2, p.1))
  obtain ⟨KS, hKS, hKS₀, hKS₁, _hKSU⟩ :=
    exists_unit_cube_face_L2_trace_normalization (n := 1) (E := Ambient q)
      (f := rawS) hε HS
      (Eventually.of_forall fun s hs => hSrows ⟨s, hs.1.le, hs.2.le⟩)
      hc₀ hc₁ hS₀ hS₁
  refine ⟨hV, ?_, ?_, KT, KS, hKT, hKT₀, hKT₁, ?_, hKS₀, hKS₁⟩
  · have heq : (∫ y in B.val, hsNormSq (DV y)) = ∫ y in Ω.val, hsNormSq (DW y) := by
      have hscale : (ε / 2) ^ (2 - (((1 + 1 : ℕ)) : ℤ)) = (1 : ℝ) := by norm_num
      rw [hscale, one_mul] at hVE
      rw [two_cube_eq_rectangle 0 ε] at hVE
      exact hVE
    exact heq.trans_le henergy
  · intro y hy
    have hcoord (j : Fin 2) : (T y) j ∈ Icc (0 : ℝ) ε := by
      change 0 ≤ ε / 2 + (ε / 2) * y j ∧ ε / 2 + (ε / 2) * y j ≤ ε
      constructor <;> nlinarith only [half_pos hε, (hy j).1, (hy j).2]
    exact hclosed (T y) (hcoord 0) (hcoord 1)
  · filter_upwards [hKS] with s hs hsI
    have hfun : (fun x => rawS (L x, (ε / 2) * (s + 1))) =
        (fun x => V (e.symm (EuclideanSpace.single (0 : Fin 1) s, x))) := by
      funext x
      exact congrArg W (affine_unit_square_split_first ε x s).symm
    have hp := hs hsI
    rw [hfun] at hp
    exact hp

end StratificationTheory
