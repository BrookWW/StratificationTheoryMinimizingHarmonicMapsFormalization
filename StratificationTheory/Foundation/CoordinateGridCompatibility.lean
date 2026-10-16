module

public import StratificationTheory.Foundation.CoordinateACLRepresentative
public import StratificationTheory.Foundation.CoordinatePermutationSobolev

/-!
# Coordinate representatives on translated finite grids

Every coordinate direction uses the same averaged-primitive formula after a
volume-preserving permutation. Translated vertices can avoid the exceptional
sets for all finitely many directions at once.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology
namespace StratificationTheory

/-- The averaged-primitive representative in a permuted coordinate direction. -/
@[expose] noncomputable def coordinatePermACLRepresentative {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (a b : ℝ)
    (u : Domain (n + 1) → Ambient q) (Du : Domain (n + 1) → Gradient (n + 1) q)
    (y : Domain (n + 1)) : Ambient q :=
  let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let U : Domain n × ℝ → Ambient q := fun z =>
    u (Q (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2)))
  let G : Domain n × ℝ → Ambient q := fun z =>
    Du (Q (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2))) (p (Fin.natAdd n (0 : Fin 1)))
  fiberACLRepresentative a b U G ((e (Q.symm y)).1, (e (Q.symm y)).2 0)

/-- The literal representative in each permuted direction has actual ambient
measurability, ambient a.e. equality, and closed-line absolute continuity with
the original weak-gradient column in that direction. -/
theorem coordinatePermACLRepresentative_of_memW12_ball {n q : ℕ}
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
    let Ω := {y : Domain (n + 1) | (e (Q.symm y)).1 ∈ S ∧ (e (Q.symm y)).2 0 ∈ Ioo a b}
    let W := coordinatePermACLRepresentative p a b u Du
    AEStronglyMeasurable W (volume.restrict Ω) ∧ W =ᵐ[volume.restrict Ω] u ∧
    ∀ᵐ x ∂volume.restrict S,
      AbsolutelyContinuousOnInterval
        (fun t => W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) a b ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) -
          W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) s))) =
          ∫ r in s..t, Du (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))
            (p (Fin.natAdd n (0 : Fin 1))) := by
  intro Q e Ω W
  have huQ := memW12_ball_coordinatePerm hR hu p
  have hrectQ : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      e.symm (x, EuclideanSpace.single (0 : Fin 1) t) ∈ ball (Q.symm z) R := by
    intro x hx t ht
    rw [← Q.preimage_ball]
    exact hrect x hx t ht
  obtain ⟨hFm, hFae, hFlines⟩ :=
    coordinateACLRepresentative_of_memW12_ball hR huQ hS hab hrectQ
  let U : Domain n × ℝ → Ambient q := fun v =>
    u (Q (e.symm (v.1, EuclideanSpace.single (0 : Fin 1) v.2)))
  let G : Domain n × ℝ → Ambient q := fun v =>
    Du (Q (e.symm (v.1, EuclideanSpace.single (0 : Fin 1) v.2))) (p (Fin.natAdd n (0 : Fin 1)))
  let F := fiberACLRepresentative a b U G
  let C : Domain (n + 1) → Domain n × ℝ := fun y =>
    ((e (Q.symm y)).1, (e (Q.symm y)).2 0)
  have hC := (measurePreserving_cylinder_coordinates n).comp Q.symm.measurePreserving
  have hCr := hC.restrict_preimage (hS.prod (measurableSet_Ioo (a := a) (b := b)))
  rw [← Measure.prod_restrict] at hCr
  have hCm : AEStronglyMeasurable F
      ((volume.restrict S).prod (volume.restrict (Ioo a b))) :=
    hFm.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono_set volume Ioo_subset_Icc_self))
  have hWF : W = F ∘ C := rfl
  have hUu (y : Domain (n + 1)) : U (C y) = u y := by
    dsimp only [U, C]
    rw [cylinder_coordinates_inverse_left n (Q.symm y), Q.apply_symm_apply]
  have hWline (x : Domain n) (t : ℝ) :
      W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) = F (x, t) := by
    rw [hWF]
    change F ((e (Q.symm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))).1,
      (e (Q.symm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))).2 0) = F (x, t)
    rw [Q.symm_apply_apply, cylinder_coordinates_inverse_right n (x, t)]
  refine ⟨hCm.comp_measurePreserving hCr, ?_, ?_⟩
  · have h := hCr.quasiMeasurePreserving.ae hFae
    filter_upwards [h] with y hy
    exact hy.trans (hUu y)
  · filter_upwards [hFlines] with x hx
    simpa only [hWline] using hx

/-- Every countable family of translated evaluation points avoids a common
volume-null exceptional set. The retained membership condition permits use
with maps known only on their actual open rectangles. -/
theorem ae_translates_preserve_ae_properties {n : ℕ} {ι κ : Type*}
    [Countable ι] [Countable κ]
    {Ω : ι → Set (Domain n)} (hΩ : ∀ i, MeasurableSet (Ω i))
    {P : ι → Domain n → Prop}
    (hP : ∀ i, ∀ᵐ y ∂volume.restrict (Ω i), P i y)
    (v : κ → Domain n) :
    ∀ᵐ a ∂volume, ∀ k i, a + v k ∈ Ω i → P i (a + v k) := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro i
  have hglobal := (ae_restrict_iff' (hΩ i)).mp (hP i)
  exact (measurePreserving_add_right volume (v k)).quasiMeasurePreserving.ae hglobal

/-- Actual Sobolev data supply compatible coordinate representatives at all
vertices of one translated countable grid. The same offset also gives whole
absolutely continuous coordinate lines through those vertices. -/
theorem exists_translated_grid_vertex_compatible_coordinate_representatives
    {n q : ℕ} {ι κ : Type*} [Countable ι] [Countable κ]
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    (p : ι → Equiv.Perm (Fin (n + 1)))
    (S : ι → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R)
    (v : κ → Domain (n + 1)) {B : Set (Domain (n + 1))}
    (hB : MeasurableSet B) (hBpos : 0 < volume B) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := fun i => {y : Domain (n + 1) |
      (e ((Q i).symm y)).1 ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let W := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) u Du
    let c := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let β := fun i y => (e ((Q i).symm y)).1
    ∃ offset ∈ B,
      (∀ k i, offset + v k ∈ Ω i →
        W i (offset + v k) = u (offset + v k) ∧
        AbsolutelyContinuousOnInterval
          (fun t => W i (c i (β i (offset + v k)) t)) (a i) (b i) ∧
        ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
          W i (c i (β i (offset + v k)) t) - W i (c i (β i (offset + v k)) s) =
            ∫ r in s..t, Du (c i (β i (offset + v k)) r) (p i (Fin.natAdd n (0 : Fin 1)))) ∧
      ∀ k i j, offset + v k ∈ Ω i → offset + v k ∈ Ω j →
        W i (offset + v k) = W j (offset + v k) := by
  intro Q e Ω W c β
  have hΩ (i : ι) : MeasurableSet (Ω i) :=
    ((hS i).preimage (continuous_fst.comp
      (e.continuous.comp (Q i).symm.continuous)).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp (e.continuous.comp (Q i).symm.continuous))).measurable)
  have hrep (i : ι) := coordinatePermACLRepresentative_of_memW12_ball
    hR hu (p i) (hS i) (hab i) (hrect i)
  have hpoint (i : ι) : ∀ᵐ y ∂volume.restrict (Ω i),
      W i y = u y ∧
      AbsolutelyContinuousOnInterval (fun t => W i (c i (β i y) t)) (a i) (b i) ∧
      ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
        W i (c i (β i y) t) - W i (c i (β i y) s) =
          ∫ r in s..t, Du (c i (β i y) r) (p i (Fin.natAdd n (0 : Fin 1))) := by
    have hcoord := ((measurePreserving_cylinder_coordinates n).comp
      (Q i).symm.measurePreserving).restrict_preimage
        ((hS i).prod (measurableSet_Ioo (a := a i) (b := b i)))
    rw [← Measure.prod_restrict] at hcoord
    have hlineProduct := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (S i)) (ν := volume.restrict (Ioo (a i) (b i)))).ae (hrep i).2.2
    have hlineAmbient := hcoord.quasiMeasurePreserving.ae hlineProduct
    filter_upwards [(hrep i).2.1, hlineAmbient] with y hy hline
    exact ⟨hy, hline⟩
  have hgood := ae_translates_preserve_ae_properties hΩ hpoint v
  have hμne : (volume : Measure (Domain (n + 1))).restrict B ≠ 0 := by
    rw [ne_eq, Measure.restrict_eq_zero]
    exact hBpos.ne'
  letI : (ae ((volume : Measure (Domain (n + 1))).restrict B)).NeBot := ae_neBot.mpr hμne
  obtain ⟨offset, hoffset, hgoodOffset⟩ :=
    ((ae_restrict_mem hB).and (ae_restrict_of_ae hgood (s := B))).exists
  refine ⟨offset, hoffset, hgoodOffset, ?_⟩
  intro k i j hi hj
  exact (hgoodOffset k i hi).1.trans (hgoodOffset k j hj).1.symm

end StratificationTheory
