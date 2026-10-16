module

public import StratificationTheory.Foundation.RadialTraceCompatibility
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Native L2 traces on the unit interval

The positive physical segment is reparameterized by its literal affine map
from [-1,1]. The same continuous curve keeps every original interior slice
class and both original endpoint classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The same original physical segment trace normalizes to [-1,1] with its
raw affine slices, both endpoint classes and whole-curve uniqueness. -/
theorem exists_unit_interval_L2_trace_of_positive_segment
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {ε : ℝ} (hε : 0 < ε) {f : α × ℝ → E}
    (H : C(Icc (0 : ℝ) ε, Lp E 2 μ))
    (hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
      ∃ hslice : MemLp (fun x => f (x, r)) 2 μ,
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r))) :
    ∃ K : C(Icc (-1 : ℝ) 1, Lp E 2 μ),
      (∀ t : Icc (-1 : ℝ) 1,
        K t = H ⟨(ε / 2) * (t.val + 1),
          mul_nonneg (half_pos hε).le (by linarith only [t.property.1]),
          by nlinarith only [t.property.2, hε]⟩) ∧
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hslice : MemLp (fun x => f (x, (ε / 2) * (t + 1))) 2 μ,
          K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, (ε / 2) * (t + 1)))) ∧
      K ⟨-1, le_rfl, by norm_num⟩ = H ⟨0, le_rfl, hε.le⟩ ∧
      K ⟨1, by norm_num, le_rfl⟩ = H ⟨ε, hε.le, le_rfl⟩ ∧
      ∀ L : C(Icc (-1 : ℝ) 1, Lp E 2 μ),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => f (x, (ε / 2) * (t + 1))) 2 μ,
            L ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, (ε / 2) * (t + 1)))) → L = K := by
  let τ : ℝ → ℝ := fun t => (ε / 2) * (t + 1)
  have hτclosed (t : Icc (-1 : ℝ) 1) : τ t.val ∈ Icc (0 : ℝ) ε := by
    constructor
    · exact mul_nonneg (half_pos hε).le (by linarith only [t.property.1])
    · dsimp only [τ]
      nlinarith only [t.property.2, hε]
  let γ : C(Icc (-1 : ℝ) 1, Icc (0 : ℝ) ε) :=
    ⟨fun t => ⟨τ t.val, hτclosed t⟩,
      ((continuous_const.mul (continuous_subtype_val.add continuous_const))).subtype_mk _⟩
  let K : C(Icc (-1 : ℝ) 1, Lp E 2 μ) := H.comp γ
  have hτ : Measure.QuasiMeasurePreserving τ (volume : Measure ℝ) volume := by
    have h := (measurePreserving_add_left (volume : Measure ℝ) (ε / 2)).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (half_pos hε).ne')
    convert h using 1
    funext t
    change (ε / 2) * (t + 1) = ε / 2 + (ε / 2) * t
    ring
  have hK : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hslice : MemLp (fun x => f (x, τ t)) 2 μ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, τ t)) := by
    filter_upwards [hτ.ae hH] with t ht htI
    have hτI : τ t ∈ Ioo (0 : ℝ) ε := by
      constructor
      · exact mul_pos (half_pos hε) (by linarith only [htI.1])
      · dsimp only [τ]
        nlinarith only [htI.2, hε]
    exact ht hτI
  refine ⟨K, fun _ => rfl, hK, ?_, ?_, ?_⟩
  · change H ⟨τ (-1), hτclosed ⟨-1, le_rfl, by norm_num⟩⟩ = _
    simp only [τ, neg_add_cancel, mul_zero]
  · change H ⟨τ 1, hτclosed ⟨1, by norm_num, le_rfl⟩⟩ = _
    have hτone : τ 1 = ε := by dsimp only [τ]; ring
    simp only [hτone]
  · intro L hL
    exact continuous_Lp_representatives_eq_of_ae_slices
      (f := fun p : α × ℝ => f (p.1, (ε / 2) * (p.2 + 1)))
      (g := fun p : α × ℝ => f (p.1, (ε / 2) * (p.2 + 1)))
      (by norm_num : (-1 : ℝ) < 1) L K hL hK
      (Eventually.of_forall fun _ _ => Filter.EventuallyEq.rfl)

end StratificationTheory
