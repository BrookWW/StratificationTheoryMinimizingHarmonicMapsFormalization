module

public import StratificationTheory.Foundation.CoordinateSobolevSlices
public import StratificationTheory.Foundation.CoordinatePermutationSobolev

/-!
# Simultaneous qualifications of original coordinate faces

Finite Sobolev ball data give one ambient almost-everywhere qualification
event for a countable family of coordinate faces. Each face keeps its original
map and the corresponding original weak-gradient columns. Face dimensions and
coordinate orderings may vary within the family.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Reindexing Euclidean coordinates preserves the original finite Sobolev
pair, with the displayed reindexing of its original weak columns. -/
theorem memW12_ball_coordinateEquiv {m n q : ℕ}
    {z : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain z R) u Du) (p : Fin m ≃ Fin n) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    MemW12 (ballDomain (Q.symm z) R) (fun x => u (Q x))
      (fun x i => Du (Q x) (p i)) := by
  have hmn : m = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr p
  subst n
  exact memW12_ball_coordinatePerm hR hu p

/-- The original weak graph on one coordinate face is a genuine ambient
almost-everywhere property of its base point. The face need not contain the
evaluation point in its tangential variables. -/
theorem ae_memW12_coordinate_face_of_memW12_ball {m k N q : ℕ}
    {z : Domain N} {R : ℝ} (hR : 0 < R)
    {u : Domain N → Ambient q} {Du : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z R) u Du) (p : Fin (m + k) ≃ Fin N)
    {S : Set (Domain m)} (hS : MeasurableSet S) (U : OpenDomain k)
    (hrect : ∀ x ∈ S, ∀ y ∈ U.val,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)).symm
          (x, y)) ∈ ball z R) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
    ∀ᵐ y ∂(volume : Measure (Domain N)),
      (e (Q.symm y)).1 ∈ S →
      MemW12 U (fun t => u (Q (e.symm ((e (Q.symm y)).1, t))))
        (fun t i => Du (Q (e.symm ((e (Q.symm y)).1, t)))
          (p (Fin.natAdd m i))) := by
  intro Q e
  have huQ := memW12_ball_coordinateEquiv hR hu p
  have hrectQ : ∀ x ∈ S, ∀ y ∈ U.val,
      e.symm (x, y) ∈ ball (Q.symm z) R := by
    intro x hx y hy
    rw [← Q.preimage_ball]
    exact hrect x hx y hy
  have hface := ae_memW12_coordinate_slice_of_memW12_ball hR huQ hS U hrectQ
  have hbase := (ae_restrict_iff' hS).mp hface
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Domain m))) (ν := (volume : Measure (Domain k)))).ae hbase
  exact ((measurePreserving_finAddEquivProd m k).comp
    Q.symm.measurePreserving).quasiMeasurePreserving.ae hprod

/-- All dimensions and coordinate orderings of a countable family qualify
on one ambient full-measure event, using only the original Sobolev ball pair.
This event can be imposed before a translated-grid choice. -/
theorem ae_memW12_coordinate_face_family_of_memW12_ball
    {N q : ℕ} {ι : Type*} [Countable ι]
    {z : Domain N} {R : ℝ} (hR : 0 < R)
    {u : Domain N → Ambient q} {Du : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z R) u Du)
    (m k : ι → ℕ) (p : ∀ i, Fin (m i + k i) ≃ Fin N)
    (S : ∀ i, Set (Domain (m i))) (hS : ∀ i, MeasurableSet (S i))
    (U : ∀ i, OpenDomain (k i))
    (hrect : ∀ i x, x ∈ S i → ∀ y ∈ (U i).val,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)).symm
          (x, y)) ∈ ball z R) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ i,
      (e i ((Q i).symm y)).1 ∈ S i →
      MemW12 (U i) (fun t => u (Q i ((e i).symm ((e i ((Q i).symm y)).1, t))))
        (fun t j => Du (Q i ((e i).symm ((e i ((Q i).symm y)).1, t)))
          (p i (Fin.natAdd (m i) j))) := by
  intro Q e
  exact ae_all_iff.mpr fun i =>
    ae_memW12_coordinate_face_of_memW12_ball hR hu (p i) (hS i) (U i) (hrect i)

end StratificationTheory
