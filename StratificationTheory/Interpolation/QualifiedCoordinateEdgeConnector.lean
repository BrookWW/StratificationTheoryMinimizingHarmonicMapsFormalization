module

public import StratificationTheory.Interpolation.CubicalEdgeUnitConnector
public import StratificationTheory.Foundation.CoordinateEdgeLocalData
public import StratificationTheory.Foundation.CoordinateGridCompatibility

/-!
# The actual coordinate edge connector from original qualified lines

Original full-line finite classes, integral increments and both raw vertex
identifications determine one normalized affine connector. The resulting
weak graph, quantitative estimates and native traces use the same map.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The fixed-coordinate version of the original edge construction can be
consumed at an already selected lattice point and its lattice neighbor. -/
theorem coordinate_edge_unit_connector_of_original_line_data {n q : ℕ}
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
    let F := fun s => rep 0 (y + s • v)
    let G := fun s => rep 1 (y + s • v)
    let f := fun s => u 0 (y + s • v)
    let h := fun s => u 1 (y + s • v)
    let g := fun s => Du 0 (y + s • v) j
    let k := fun s => Du 1 (y + s • v) j
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let a₁ : Domain 1 := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun y : Domain 2 => A + (ε / 2) • y
    let L := fun x : Domain 1 => a₁ + (ε / 2) • x
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
    F 0 = u 0 y ∧ F ε = u 0 (y + ε • v) ∧
      G 0 = u 1 y ∧ G ε = u 1 (y + ε • v) ∧
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
  intro Q e₀ j v β rep line ha hb hU hD hAE hValues hInc hRaw₀ hRawε
    F G f h g k e B C a₁ A T L W DW V DV chord D E
  obtain ⟨hf, hg, hFAC, hFae, _hFN, hfN, hFinc, hF₀, hFε⟩ :=
    coordinate_edge_original_local_data (n := n) (q := q) p y hε
      (u := u 0) (R := rep 0) (Du := Du 0) (N := N) ha hb
      (hU 0) (hD 0) (hAE 0) (hValues 0) (hInc 0) (hRaw₀ 0) (hRawε 0)
  obtain ⟨hh, hk, hGAC, hGae, _hGN, hhN, hGinc, hG₀, hGε⟩ :=
    coordinate_edge_original_local_data (n := n) (q := q) p y hε
      (u := u 1) (R := rep 1) (Du := Du 1) (N := N) ha hb
      (hU 1) (hD 1) (hAE 1) (hValues 1) (hInc 1) (hRaw₀ 1) (hRawε 1)
  have hconnector := exists_unit_affine_edge_connector (q := q) (F := F) (G := G)
    (f := f) (h := h) (g := g) (k := k) hε hf hh hg hk hFAC hGAC
    hFae hGae hFinc hGinc hN hfN hhN
  exact ⟨hF₀, hFε, hG₀, hGε, hconnector⟩

end StratificationTheory
