module

public import StratificationTheory.Interpolation.QualifiedCoordinateEdgeConnector
public import StratificationTheory.Foundation.CoordinateEdgeLocalData
public import StratificationTheory.Foundation.CoordinateACLQualification

/-!
# Actual affine edge connectors from original ball maps

The original ball Sobolev pair produces almost everywhere the literal
coordinate edge connector with its original derivative, unit energy and
target-distance bounds and all four native boundary traces. The spatial
boundary chords have the original raw values at both endpoint vertices.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original ball maps internally produce all line qualifications of the
same affine edge connector. Both original endpoint vertex identifications
hold in the same full-measure origin event. -/
theorem ae_original_coordinate_edge_unit_connector {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (hu : ∀ l, MemW12 (ballDomain z R) (u l) (Du l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (huN : ∀ l, ∀ᵐ y ∂volume.restrict (ball z R), u l y ∈ N)
    (p : Equiv.Perm (Fin (n + 1)))
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R)
    {ε : ℝ} (hε : 0 < ε) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := fun y => (e₀ (Q.symm y)).1
    let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
    ∀ᵐ y ∂volume,
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
    β y ∈ S → y j ∈ Ioo a b → y j + ε ∈ Ioo a b →
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
  intro Q e₀ j v β rep
  let line := fun (y : Domain (n + 1)) (t : ℝ) =>
    Q (e₀.symm (β y, EuclideanSpace.single (0 : Fin 1) t))
  let Ω := {y : Domain (n + 1) | β y ∈ S ∧ (e₀ (Q.symm y)).2 0 ∈ Ioo a b}
  let P : Domain (n + 1) → Prop := fun y => ∀ l : Fin 2, y ∈ Ω →
    rep l y = u l y ∧
    MemLp (fun t => u l (line y t)) 2 (volume.restrict (Ioo a b)) ∧
    MemLp (fun t => Du l (line y t) j) 2 (volume.restrict (Ioo a b)) ∧
    AbsolutelyContinuousOnInterval (fun t => rep l (line y t)) a b ∧
    (fun t => rep l (line y t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => u l (line y t)) ∧
    (∀ t ∈ Icc a b, rep l (line y t) ∈ N) ∧
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      rep l (line y t) - rep l (line y s) = ∫ r in s..t, Du l (line y r) j
  have hACLraw := ae_all_iff.mpr fun l : Fin 2 =>
    ae_coordinate_acl_closed_target_qualification hR (hu l) hN.isClosed (huN l)
      (fun _ : Unit => p) (fun _ => S) (fun _ => hS) (fun _ => a) (fun _ => b)
      (fun _ => hab) (fun _ => hrect)
  have hACL : ∀ᵐ y ∂volume, P y := by
    filter_upwards [hACLraw] with y hy
    exact fun l => hy l ()
  generalize hPdef : P = P₀ at hACL
  have hshift := (measurePreserving_add_right (volume : Measure (Domain (n + 1)))
    (ε • v)).quasiMeasurePreserving.ae (p := P₀) hACL
  filter_upwards [hACL, hshift] with y hy hyshift
  rw [← hPdef] at hy hyshift
  intro F G f h g k e B C a₁ A T L W DW V DV chord D E hβ hyj hyε
  have hyΩ : β y ∈ S ∧ (e₀ (Q.symm y)).2 0 ∈ Ioo a b := by
    have hj : (e₀ (Q.symm y)).2 0 = y j := coordinate_split_last_eq p y
    exact ⟨hβ, hj.symm ▸ hyj⟩
  have hy'Ω : β (y + ε • v) ∈ S ∧ (e₀ (Q.symm (y + ε • v))).2 0 ∈ Ioo a b := by
    have hc := coordinate_normal_translation_coordinates p y ε
    have hβ' : β (y + ε • v) = β y := hc.1
    have ht' : (e₀ (Q.symm (y + ε • v))).2 0 = y j + ε := hc.2
    exact ⟨hβ'.symm ▸ hβ, ht'.symm ▸ hyε⟩
  have hresult := coordinate_edge_unit_connector_of_original_line_data
    (n := n) (q := q) p y a b ε hε u Du hN.isClosed hyj.1.le hyε.2.le
    (fun l => (hy l hyΩ).2.1)
    (fun l => (hy l hyΩ).2.2.1)
    (fun l => (hy l hyΩ).2.2.2.2.1)
    (fun l => (hy l hyΩ).2.2.2.2.2.1)
    (fun l => (hy l hyΩ).2.2.2.2.2.2)
    (fun l => (hy l hyΩ).1) (fun l => (hyshift l hy'Ω).1)
  exact hresult

end StratificationTheory
