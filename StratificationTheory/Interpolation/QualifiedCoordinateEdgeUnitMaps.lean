module

public import StratificationTheory.Interpolation.QualifiedCoordinateEdgeConnector
public import StratificationTheory.Interpolation.CoordinateEdgeUnitMaps

/-!
# Original raw boundary classes of the named coordinate connector

The literal coordinate connector maps retain the original finite energy
and distance bounds. Both spatial endpoint classes are identified with
the original raw vertex chords on the whole native unit edge.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The original line qualifications give the named actual maps and all
four raw boundary classes, including the original raw vertex chords. -/
theorem coordinate_edge_unit_maps_of_original_line_data {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (y : Domain (n + 1))
    (a b ε : ℝ) (hε : 0 < ε)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {N : Set (Ambient q)} (hN : IsClosed N) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := (e₀ (Q.symm y)).1
    let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
    let line := fun t => Q (e₀.symm (β, EuclideanSpace.single (0 : Fin 1) t))
    a ≤ y j → y j + ε ≤ b →
    (∀ l, MemLp (fun t => u l (line t)) 2 (volume.restrict (Ioo a b))) →
    (∀ l, MemLp (fun t => Du l (line t) j) 2 (volume.restrict (Ioo a b))) →
    (∀ l, (fun t => rep l (line t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => u l (line t))) →
    (∀ l t, t ∈ Icc a b → rep l (line t) ∈ N) →
    (∀ l s, s ∈ Icc a b → ∀ t, t ∈ Icc a b →
      rep l (line t) - rep l (line s) = ∫ r in s..t, Du l (line r) j) →
    (∀ l, rep l y = u l y) → (∀ l, rep l (y + ε • v) = u l (y + ε • v)) →
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let edge := fun (l : Fin 2) (x : Domain 1) =>
      u l (y + (ε / 2 + (ε / 2) * x 0) • v)
    let V := coordinateEdgeUnitMap p a b ε u Du y
    let DV := coordinateEdgeUnitGradient p a b ε u Du y
    let D := ∫ s in Ioo (0 : ℝ) ε, ‖u 0 (y + s • v) - u 1 (y + s • v)‖ ^ 2
    let E := ∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2 + ‖Du 1 (y + s • v) j‖ ^ 2
    MemW12 B V DV ∧
      (∫ z in B.val, hsNormSq (DV z)) ≤
        (ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖Du 1 (y + s • v) j‖ ^ 2) + ε⁻¹ * D ∧
      (∀ z : Domain 2, (∀ j, z j ∈ Icc (-1 : ℝ) 1) →
        (infDist (V z) N) ^ 2 ≤ D / ε + Real.sqrt (2 * D * E)) ∧
      ∃ HT : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        ∃ HS : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
            2 (volume.restrict C), HT ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp
              (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∃ h₀ : MemLp (edge 0) 2 (volume.restrict C),
          HT ⟨-1, le_rfl, by norm_num⟩ = h₀.toLp (edge 0)) ∧
        (∃ h₁ : MemLp (edge 1) 2 (volume.restrict C),
          HT ⟨1, by norm_num, le_rfl⟩ = h₁.toLp (edge 1)) ∧
        (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (e.symm (EuclideanSpace.single (0 : Fin 1) s, x)))
            2 (volume.restrict C), HS ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp
              (fun x => V (e.symm (EuclideanSpace.single (0 : Fin 1) s, x)))) ∧
        (∃ h₀ : MemLp (coordinateEdgeRawUnitChord p ε u y 0) 2 (volume.restrict C),
          HS ⟨-1, le_rfl, by norm_num⟩ = h₀.toLp (coordinateEdgeRawUnitChord p ε u y 0)) ∧
        (∃ h₁ : MemLp (coordinateEdgeRawUnitChord p ε u y ε) 2 (volume.restrict C),
          HS ⟨1, by norm_num, le_rfl⟩ = h₁.toLp (coordinateEdgeRawUnitChord p ε u y ε)) := by
  intro Q e₀ j v β rep line ha hb hU hD hAE hValues hInc hRaw₀ hRawε
    e B C edge V DV D E
  obtain ⟨hF₀, hFε, hG₀, hGε, hV, hEnergy, hDist, HT, HS,
      hHT, hHT₀, hHT₁, hHS, hHS₀, hHS₁⟩ :=
    coordinate_edge_unit_connector_of_original_line_data (n := n) (q := q)
      p y a b ε hε u Du hN ha hb hU hD hAE hValues hInc hRaw₀ hRawε
  let A₂ : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
  let L₁ : Domain 1 → Domain 1 := fun x =>
    (WithLp.toLp 2 (fun _ : Fin 1 => ε / 2)) + (ε / 2) • x
  let rawMap : Domain 2 → Ambient q :=
    (fun z : Domain 2 =>
      (1 - (e z).2 0 / ε) • rep 0 (y + (e z).1 0 • v) +
        ((e z).2 0 / ε) • rep 1 (y + (e z).1 0 • v)) ∘
      (fun z => A₂ + (ε / 2) • z)
  have hrawMap : rawMap = V := rfl
  let rawEdge := fun (l : Fin 2) => (fun x : Domain 1 => u l (y + x 0 • v)) ∘ L₁
  have hrawEdge (l : Fin 2) : rawEdge l = edge l := rfl
  let rawChord := fun (side : ℝ) =>
    (fun x : Domain 1 => (1 - x 0 / ε) • rep 0 (y + side • v) +
      (x 0 / ε) • rep 1 (y + side • v)) ∘ L₁
  have hchord (side : ℝ)
      (hF : rep 0 (y + side • v) = u 0 (y + side • v))
      (hG : rep 1 (y + side • v) = u 1 (y + side • v)) : rawChord side = coordinateEdgeRawUnitChord p ε u y side := by
    funext x
    change (1 - (ε / 2 + (ε / 2) * x 0) / ε) • rep 0 (y + side • v) +
      ((ε / 2 + (ε / 2) * x 0) / ε) • rep 1 (y + side • v) = _
    exact congrArg₂ (fun z w => (1 - (ε / 2 + (ε / 2) * x 0) / ε) • z +
      ((ε / 2 + (ε / 2) * x 0) / ε) • w) hF hG
  refine ⟨?_, ?_, ?_, HT, HS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold V DV coordinateEdgeUnitMap coordinateEdgeUnitGradient
    exact hV
  · simpa only [DV, coordinateEdgeUnitGradient, Function.comp_def] using hEnergy
  · simpa only [V, coordinateEdgeUnitMap, Function.comp_def] using hDist
  · rw [← hrawMap]
    exact hHT
  · rw [← hrawEdge 0]
    exact hHT₀
  · rw [← hrawEdge 1]
    exact hHT₁
  · rw [← hrawMap]
    exact hHS
  · have hc₀ := hchord 0 (by simpa only [zero_smul, add_zero] using hF₀)
        (by simpa only [zero_smul, add_zero] using hG₀)
    rw [← hc₀]
    exact hHS₀
  · have hc₁ := hchord ε hFε hGε
    rw [← hc₁]
    exact hHS₁

end StratificationTheory
