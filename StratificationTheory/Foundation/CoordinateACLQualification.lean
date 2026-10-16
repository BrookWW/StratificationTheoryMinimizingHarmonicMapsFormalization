module

public import StratificationTheory.Foundation.CoordinateClosedTargetACL
public import StratificationTheory.Foundation.CoordinateClosedTargetLineL2

/-!
# One ambient qualification event for original closed-target ACL lines

The canonical averaged-primitive representatives of a countable family of
coordinate lines retain the raw map, original derivative increments and
closed-target values. All qualifications hold on one ambient full-measure
event, before any translated grid is selected.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original ball Sobolev data with their original closed-target constraint
produce one ambient qualification event for a countable family of canonical
coordinate ACL representatives and the original raw line data. -/
theorem ae_coordinate_acl_closed_target_qualification
    {n q : ℕ} {ι : Type*} [Countable ι]
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q}
    {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {N : Set (Ambient q)} (hN : IsClosed N)
    (huN : ∀ᵐ y ∂volume.restrict (ball z R), u y ∈ N)
    (p : ι → Equiv.Perm (Fin (n + 1)))
    (S : ι → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := fun i => {y : Domain (n + 1) |
      (e ((Q i).symm y)).1 ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let W := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) u Du
    let c := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let β := fun i y => (e ((Q i).symm y)).1
    ∀ᵐ y ∂(volume : Measure (Domain (n + 1))), ∀ i, y ∈ Ω i →
      W i y = u y ∧
      MemLp (fun t => u (c i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
      MemLp (fun t => Du (c i (β i y) t) (p i (Fin.natAdd n (0 : Fin 1))))
        2 (volume.restrict (Ioo (a i) (b i))) ∧
      AbsolutelyContinuousOnInterval (fun t => W i (c i (β i y) t)) (a i) (b i) ∧
      (fun t => W i (c i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
        (fun t => u (c i (β i y) t)) ∧
      (∀ t ∈ Icc (a i) (b i), W i (c i (β i y) t) ∈ N) ∧
      ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
        W i (c i (β i y) t) - W i (c i (β i y) s) =
          ∫ r in s..t, Du (c i (β i y) r) (p i (Fin.natAdd n (0 : Fin 1))) := by
  intro Q e Ω W c β
  apply ae_all_iff.mpr
  intro i
  have hrep := coordinatePermACLRepresentative_closed_target_of_memW12_ball
    hR hu hN huN (p i) (hS i) (hab i) (hrect i)
  have hLp := ae_coordinatePerm_line_memLp_two_of_memW12_ball
    hR hu (p i) (hS i) (hab i) (hrect i)
  have hΩ : MeasurableSet (Ω i) :=
    ((hS i).preimage (continuous_fst.comp
      (e.continuous.comp (Q i).symm.continuous)).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp (e.continuous.comp (Q i).symm.continuous))).measurable)
  apply (ae_restrict_iff' hΩ).mp
  have hcoord := ((measurePreserving_cylinder_coordinates n).comp
    (Q i).symm.measurePreserving).restrict_preimage
      ((hS i).prod (measurableSet_Ioo (a := a i) (b := b i)))
  rw [← Measure.prod_restrict] at hcoord
  have hlineProd := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (S i)) (ν := volume.restrict (Ioo (a i) (b i)))).ae hrep.2.2
  have hLpProd := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (S i)) (ν := volume.restrict (Ioo (a i) (b i)))).ae hLp
  have hline := hcoord.quasiMeasurePreserving.ae hlineProd
  have hlineLp := hcoord.quasiMeasurePreserving.ae hLpProd
  filter_upwards [hrep.2.1, hlineLp, hline] with y hy hLy hFy
  exact ⟨hy, hLy.1, hLy.2, hFy.1, hFy.2.1, hFy.2.2.1, hFy.2.2.2⟩

end StratificationTheory
