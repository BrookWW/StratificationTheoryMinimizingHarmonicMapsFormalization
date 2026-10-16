module
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry
public import StratificationTheory.Foundation.IntervalSobolevTranslation

/-!
# The actual paired energy identity on a translated coordinate edge

Original line L2 derivative data give actual squared-norm integrability on
the physical subedge. The paired integral is therefore the sum of the two
original integrals.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original full-line L2 qualifications yield the actual physical-edge
squared-norm integrability and the paired energy identity. -/
theorem coordinate_line_pair_energy_integrable {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (y : Domain (n + 1))
    (a b ε : ℝ) (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := (e (Q.symm y)).1
    let line := fun t => Q (e.symm (β, EuclideanSpace.single (0 : Fin 1) t))
    a ≤ y j → y j + ε ≤ b →
    (∀ l, MemLp (fun t => Du l (line t) j) 2 (volume.restrict (Ioo a b))) →
    (∀ l, IntegrableOn (fun s => ‖Du l (y + s • v) j‖ ^ 2) (Ioo (0 : ℝ) ε)) ∧
      (∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2 + ‖Du 1 (y + s • v) j‖ ^ 2) =
        (∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖Du 1 (y + s • v) j‖ ^ 2 := by
  intro Q e j v β line ha hb hD
  have hline (s : ℝ) : line (y j + s) = y + s • v := by
    simpa only [line, j, add_sub_cancel_left] using coordinate_line_eq_add_normal p y (y j + s)
  have hLocal (l : Fin 2) : MemLp (fun s => Du l (y + s • v) j)
      2 (volume.restrict (Ioo (0 : ℝ) ε)) := by
    have h := memLp_translated_subinterval ha hb (hD l)
    simpa only [hline] using h
  have hI (l : Fin 2) : IntegrableOn (fun s => ‖Du l (y + s • v) j‖ ^ 2) (Ioo (0 : ℝ) ε) :=
    (hLocal l).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  exact ⟨hI, integral_add (hI 0) (hI 1)⟩

end StratificationTheory
