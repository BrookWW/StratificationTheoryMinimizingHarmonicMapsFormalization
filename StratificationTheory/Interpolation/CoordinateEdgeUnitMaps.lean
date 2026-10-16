module

public import StratificationTheory.Foundation.CoordinateGridCompatibility

/-!
# Literal coordinate edge connector maps

The canonical original line representatives determine the affine unit-face
map and its original gradient columns. Raw vertex chords are defined for
every physical side parameter with the same coordinate direction.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The actual affine unit-square map of the canonical coordinate lines. -/
@[expose] noncomputable def coordinateEdgeUnitMap {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (a b ε : ℝ)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (y : Domain (n + 1)) (z : Domain 2) : Ambient q :=
  let j := p (Fin.natAdd n (0 : Fin 1))
  let v := EuclideanSpace.single j (1 : ℝ)
  let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
  let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  let s := (e (A + (ε / 2) • z)).1 0
  let θ := (e (A + (ε / 2) • z)).2 0 / ε
  (1 - θ) • rep 0 (y + s • v) + θ • rep 1 (y + s • v)

/-- The original spatial column and affine temporal column in the same
literal normalized edge chart. -/
@[expose] noncomputable def coordinateEdgeUnitGradient {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (a b ε : ℝ)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (y : Domain (n + 1)) (z : Domain 2) : Gradient 2 q :=
  let j := p (Fin.natAdd n (0 : Fin 1))
  let v := EuclideanSpace.single j (1 : ℝ)
  let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
  let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  let s := (e (A + (ε / 2) • z)).1 0
  let θ := (e (A + (ε / 2) • z)).2 0 / ε
  fun k => (ε / 2) • Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
    (fun _ : Fin 1 => (1 - θ) • Du 0 (y + s • v) j + θ • Du 1 (y + s • v) j)
    (fun _ : Fin 1 => ε⁻¹ • (rep 1 (y + s • v) - rep 0 (y + s • v))) k

/-- The raw vertex chord at any physical side of the local edge. The
formula is total in the side parameter and uses the same affine unit time. -/
@[expose] noncomputable def coordinateEdgeRawUnitChord {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (ε : ℝ)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (y : Domain (n + 1)) (side : ℝ) (x : Domain 1) : Ambient q :=
  let j := p (Fin.natAdd n (0 : Fin 1))
  let v := EuclideanSpace.single j (1 : ℝ)
  let τ := ε / 2 + (ε / 2) * x 0
  (1 - τ / ε) • u 0 (y + side • v) + (τ / ε) • u 1 (y + side • v)

/-- The map formula holds at every unit-coordinate argument. -/
theorem coordinateEdgeUnitMap_eq {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (a b ε : ℝ)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (y : Domain (n + 1)) (z : Domain 2) :
    coordinateEdgeUnitMap p a b ε u Du y z =
      let j := p (Fin.natAdd n (0 : Fin 1))
      let v := EuclideanSpace.single j (1 : ℝ)
      let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
      let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
      let s := (e (A + (ε / 2) • z)).1 0
      let θ := (e (A + (ε / 2) • z)).2 0 / ε
      (1 - θ) • rep 0 (y + s • v) + θ • rep 1 (y + s • v) := rfl

/-- Every displayed original column is that of the same map chart. -/
theorem coordinateEdgeUnitGradient_eq {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (a b ε : ℝ)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (y : Domain (n + 1)) (z : Domain 2) :
    coordinateEdgeUnitGradient p a b ε u Du y z =
      let j := p (Fin.natAdd n (0 : Fin 1))
      let v := EuclideanSpace.single j (1 : ℝ)
      let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
      let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
      let s := (e (A + (ε / 2) • z)).1 0
      let θ := (e (A + (ε / 2) • z)).2 0 / ε
      fun k => (ε / 2) • Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - θ) • Du 0 (y + s • v) j + θ • Du 1 (y + s • v) j)
        (fun _ : Fin 1 => ε⁻¹ • (rep 1 (y + s • v) - rep 0 (y + s • v))) k := rfl

/-- The raw chord formula holds for every side and every unit time. -/
theorem coordinateEdgeRawUnitChord_eq {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (ε : ℝ)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (y : Domain (n + 1)) (side : ℝ) (x : Domain 1) :
    coordinateEdgeRawUnitChord p ε u y side x =
      let j := p (Fin.natAdd n (0 : Fin 1))
      let v := EuclideanSpace.single j (1 : ℝ)
      let τ := ε / 2 + (ε / 2) * x 0
      (1 - τ / ε) • u 0 (y + side • v) + (τ / ε) • u 1 (y + side • v) := rfl

end StratificationTheory
