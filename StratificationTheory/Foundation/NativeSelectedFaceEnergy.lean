module

public import StratificationTheory.Foundation.OriginalGridEnergyChannels
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Actual selected-face energies under the original scalar grid channels

The native weak columns of an original coordinate face are a subset of the
original ambient columns. Their actual Dirichlet energy, and the actual map
discrepancy, are bounded by the same two original scalar channels used by the
selected grid.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Selecting distinct original gradient columns can only decrease their
actual Hilbert--Schmidt squared norm. -/
theorem hsNormSq_coordinate_embedding_le {N k q : ℕ}
    (face : Fin k ↪ Fin N) (D : Gradient N q) :
    hsNormSq (fun j : Fin k => D (face j)) ≤ hsNormSq D := by
  classical
  unfold hsNormSq
  calc
    (∑ j : Fin k, ‖D (face j)‖ ^ 2) =
        ∑ i ∈ Finset.univ.image face, ‖D i‖ ^ 2 :=
      (Finset.sum_image (s := Finset.univ) (g := face) (f := fun i : Fin N => ‖D i‖ ^ 2)
        (fun i _ j _ hij => face.injective hij)).symm
    _ ≤ ∑ i : Fin N, ‖D i‖ ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg ‖D i‖

/-- The actual two native face-column energies are bounded by the original
ambient HS-sum channel on the same physical face. Only carrier inclusion is
needed; no measurability of the ambient channel on a fixed face is assumed. -/
theorem original_coordinate_face_energy_le_native_channel {N k q : ℕ}
    {z : Domain N} {R : ℝ} (face : Fin k ↪ Fin N)
    (A : Domain k → Domain N) {U V : Set (Domain k)} (hU : MeasurableSet U)
    (hUV : U ⊆ V) (hImage : ∀ t ∈ U, A t ∈ ball z R)
    (Du Dv : Domain N → Gradient N q) :
    let E := (ball z R).indicator (fun x => ENNReal.ofReal (hsNormSq (Du x) + hsNormSq (Dv x)))
    dirichletEnergy (fun t j => Du (A t) (face j)) U +
      dirichletEnergy (fun t j => Dv (A t) (face j)) U ≤ ∫⁻ t in V, E (A t) := by
  intro E
  have hpoint (t : Domain k) (ht : t ∈ U) :
      ENNReal.ofReal (hsNormSq (fun j : Fin k => Du (A t) (face j))) +
        ENNReal.ofReal (hsNormSq (fun j : Fin k => Dv (A t) (face j))) ≤ E (A t) := by
    dsimp only [E]
    rw [Set.indicator_of_mem (hImage t ht),
      ← ENNReal.ofReal_add (hsNormSq_nonneg _) (hsNormSq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (add_le_add
      (hsNormSq_coordinate_embedding_le face (Du (A t)))
      (hsNormSq_coordinate_embedding_le face (Dv (A t))))
  calc
    _ ≤ ∫⁻ t in U,
        ENNReal.ofReal (hsNormSq (fun j : Fin k => Du (A t) (face j))) +
          ENNReal.ofReal (hsNormSq (fun j : Fin k => Dv (A t) (face j))) :=
      le_lintegral_add _ _
    _ ≤ ∫⁻ t in U, E (A t) := setLIntegral_mono' hU hpoint
    _ ≤ _ := lintegral_mono_set hUV

/-- Actual energies of a finite family of contained original faces are
controlled by the same total native scalar channel selected on the lattice.
No face incidence or gradient witness is changed in this summation. -/
theorem finite_original_coordinate_face_energy_le_total_channel
    {N k q : ℕ} {κ : Type*} {z : Domain N} {R : ℝ}
    (face : Fin k ↪ Fin N) (A : κ → Domain k → Domain N)
    {U V : Set (Domain k)} (hU : MeasurableSet U) (hUV : U ⊆ V)
    (Z : Finset κ) (hImage : ∀ a ∈ Z, ∀ t ∈ U, A a t ∈ ball z R)
    (Du Dv : Domain N → Gradient N q) :
    let E := (ball z R).indicator (fun x => ENNReal.ofReal (hsNormSq (Du x) + hsNormSq (Dv x)))
    (∑ a ∈ Z,
      (dirichletEnergy (fun t j => Du (A a t) (face j)) U +
        dirichletEnergy (fun t j => Dv (A a t) (face j)) U)) ≤
      ∑' a : κ, ∫⁻ t in V, E (A a t) := by
  classical
  intro E
  calc
    _ ≤ ∑ a ∈ Z, ∫⁻ t in V, E (A a t) :=
      Finset.sum_le_sum fun a ha =>
        original_coordinate_face_energy_le_native_channel face (A a) hU hUV (hImage a ha) Du Dv
    _ ≤ _ := ENNReal.sum_le_tsum Z

/-- Actual original face L2 data identify the real discrepancy integral and
bound it by the same original native discrepancy channel. -/
theorem original_coordinate_face_discrepancy_le_native_channel {N k q : ℕ}
    {z : Domain N} {R : ℝ} (A : Domain k → Domain N)
    {U V : Set (Domain k)} (hU : MeasurableSet U) (hUV : U ⊆ V)
    (hImage : ∀ t ∈ U, A t ∈ ball z R)
    {u v : Domain N → Ambient q}
    (hu : MemLp (fun t => u (A t)) 2 (volume.restrict U))
    (hv : MemLp (fun t => v (A t)) 2 (volume.restrict U)) :
    let D := (ball z R).indicator (fun x => ENNReal.ofReal (‖u x - v x‖ ^ 2))
    ENNReal.ofReal (∫ t in U, ‖u (A t) - v (A t)‖ ^ 2) ≤ ∫⁻ t in V, D (A t) := by
  intro D
  have hDI := (hu.sub hv).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  calc
    _ = ∫⁻ t in U, ENNReal.ofReal (‖u (A t) - v (A t)‖ ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal hDI (Eventually.of_forall fun _ => sq_nonneg _)
    _ ≤ ∫⁻ t in U, D (A t) := by
      apply setLIntegral_mono' hU
      intro t ht
      exact le_of_eq (Set.indicator_of_mem (hImage t ht) (fun x => ENNReal.ofReal (‖u x - v x‖ ^ 2))).symm
    _ ≤ _ := lintegral_mono_set hUV

end StratificationTheory
