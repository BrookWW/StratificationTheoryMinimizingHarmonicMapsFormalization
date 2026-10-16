module

public import StratificationTheory.Foundation.CoordinatePermutationSobolev
public import StratificationTheory.Foundation.CoordinateLineACL

/-!
# Original coordinate-line L2 data

Almost every line of a contained permuted rectangle retains the original
map and its original directional weak-gradient column as L2 functions.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

/-- Permuting a coordinate direction and slicing the actual Sobolev ball
gives L2 membership for both original line data. -/
theorem ae_coordinatePerm_line_memLp_two_of_memW12_ball {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (p : Equiv.Perm (Fin (n + 1)))
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ᵐ x ∂volume.restrict S,
      MemLp (fun t => u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))
        2 (volume.restrict (Ioo a b)) ∧
      MemLp (fun t => Du (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
        (p (Fin.natAdd n (0 : Fin 1)))) 2 (volume.restrict (Ioo a b)) := by
  intro Q e
  have huQ := memW12_ball_coordinatePerm hR hu p
  have hrectQ : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      e.symm (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball (Q.symm z) R := by
    intro x hx t ht
    rw [← Q.preimage_ball]
    exact hrect x hx t ht
  have hline := ae_coordinateLine_exists_ac_of_memW12_ball hR huQ hS hab hrectQ
  filter_upwards [hline] with x hx
  exact ⟨hx.1, hx.2.1⟩

end StratificationTheory
