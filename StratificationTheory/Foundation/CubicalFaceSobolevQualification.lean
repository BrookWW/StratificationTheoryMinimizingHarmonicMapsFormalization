module

public import StratificationTheory.Foundation.TranslatedCoordinateFaceSobolev
public import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fintype

/-!
# Original weak graphs for arbitrary coordinate-face embeddings

Every coordinate embedding extends to an ambient coordinate ordering. The
same translated-face weak graph therefore has the literal finite-coordinate
formula used by the cubical scalar sampler and retains its original columns.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

private theorem face_split_basis (m k : ℕ) (j : Fin k) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)).symm
      (0, EuclideanSpace.single j (1 : ℝ)) =
        EuclideanSpace.single (Fin.natAdd m j) 1 := by
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext i
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

/-- A coordinate face parameterization has the literal finite-coordinate
formula, including the original order of the tangential variables. -/
theorem coordinate_face_embedding_eq_sum {m k N : ℕ} (p : Fin (m + k) ≃ Fin N)
    (t : Domain k) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)).symm (0, t)) =
        ∑ j : Fin k, t j • EuclideanSpace.single (p (Fin.natAdd m j)) (1 : ℝ) := by
  let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := k)
  let L : Domain k →L[ℝ] Domain N := Q.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Domain m) (Domain k)))
  have ht : t = ∑ j : Fin k, t j • EuclideanSpace.single j (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  have hL (j : Fin k) : L (EuclideanSpace.single j (1 : ℝ)) =
      EuclideanSpace.single (p (Fin.natAdd m j)) 1 := by
    change Q (e.symm (0, EuclideanSpace.single j (1 : ℝ))) = _
    rw [face_split_basis, LinearIsometryEquiv.piLpCongrLeft_single]
  change L t = _
  calc
    L t = L (∑ j : Fin k, t j • EuclideanSpace.single j (1 : ℝ)) := congrArg L ht
    _ = ∑ j : Fin k, t j • L (EuclideanSpace.single j (1 : ℝ)) := by
      rw [map_sum]
      simp only [map_smul]
    _ = _ := by simp only [hL]

/-- The literal coordinate sum in a native face chart is exactly the shift
kernel in the scalar mixed-face sampler. -/
theorem coordinate_face_embedding_sum_eq_toLp {N k : ℕ}
    (face : Fin k ↪ Fin N) (t : Domain k) :
    (∑ j : Fin k, t j • EuclideanSpace.single (face j) (1 : ℝ)) =
      WithLp.toLp 2 (fun l : Fin N => ∑ j : Fin k, if face j = l then t j else 0) := by
  ext l
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  change (∑ j : Fin k, t j * (Pi.single (face j) (1 : ℝ) : Fin N → ℝ) l) = _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : face j = l
  · simp only [h, Pi.single_eq_same, ite_true, mul_one]
  · have h' : l ≠ face j := Ne.symm h
    simp only [h, Pi.single_eq_of_ne h', ite_false, mul_zero]

private theorem exists_coordinate_face_ordering {N k : ℕ} (face : Fin k ↪ Fin N) :
    ∃ p : Fin (N - k + k) ≃ Fin N, ∀ j : Fin k, p (Fin.natAdd (N - k) j) = face j := by
  have hkN : k ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective face face.injective
  let c : Fin k → Fin N := fun j => Fin.cast (Nat.sub_add_cancel hkN) (Fin.natAdd (N - k) j)
  have hc : Function.Injective c :=
    (finCongr (Nat.sub_add_cancel hkN)).injective.comp (Fin.natAddEmb (N - k)).injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair c face hc face.injective
  refine ⟨(finCongr (Nat.sub_add_cancel hkN)).trans σ, ?_⟩
  exact fun j => hσ j

/-- Original ball data qualify every member of a countable family of actual
coordinate-face embeddings, for every subsequently chosen contained open
face. The raw face formula is the scalar sampler's literal coordinate sum;
the weak columns are the matching original ambient columns. -/
theorem ae_memW12_cubical_face_family_of_memW12_ball
    {N q : ℕ} {ι : Type*} [Countable ι]
    {z : Domain N} {R : ℝ} (hR : 0 < R)
    {u : Domain N → Ambient q} {Du : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z R) u Du)
    (k : ι → ℕ) (face : ∀ i, Fin (k i) ↪ Fin N) :
    let A := fun i (y : Domain N) (t : Domain (k i)) =>
      y + ∑ j : Fin (k i), t j • EuclideanSpace.single (face i j) (1 : ℝ)
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ (i : ι) (U : OpenDomain (k i)),
      (∀ t ∈ U.val, A i y t ∈ ball z R) →
      MemW12 U (fun t => u (A i y t)) (fun t j => Du (A i y t) (face i j)) := by
  classical
  intro A
  choose p hp using fun i => exists_coordinate_face_ordering (face i)
  have hfaces := ae_memW12_all_translated_coordinate_faces_of_memW12_ball
    hR hu (fun i => N - k i) k p
  have hA (i : ι) (y : Domain N) (t : Domain (k i)) :
      y + (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N - k i) (m := k i)).symm (0, t)) =
          A i y t := by
    rw [coordinate_face_embedding_eq_sum]
    simp only [hp]
    rfl
  filter_upwards [hfaces] with y hy
  intro i U hU
  have hU' : ∀ t ∈ U.val,
      y + (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N - k i) (m := k i)).symm (0, t)) ∈
          ball z R := by
    simpa only [hA] using hU
  simpa only [hA, hp] using hy i U hU'

end StratificationTheory
