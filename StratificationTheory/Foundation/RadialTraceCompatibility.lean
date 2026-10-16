module

public import StratificationTheory.Foundation.AngularL2Membership
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra
import StratificationTheory.Foundation.IntervalClosedConstraints
import StratificationTheory.Foundation.PolarAETransport

/-!
# Compatibility of actual radial L2 representatives

These conditional uniqueness tools compare already constructed continuous L2
curves by their original interior slice classes. Common radial bands give
agreement on the entire closed overlap. Ambient volume-a.e. changes preserve
those classes and hence the whole closed-interval curve.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Conditional continuous L2 representatives of a.e. equal original slices
agree on the whole nondegenerate closed interval, including its endpoints. -/
theorem continuous_Lp_representatives_eq_of_ae_slices
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {a b : ℝ} (hab : a < b)
    {f g : α × ℝ → E} (H K : C(Icc a b, Lp E 2 μ))
    (hH : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ => f (θ, r)) 2 μ,
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ => f (θ, r)))
    (hK : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ => g (θ, r)) 2 μ,
        K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ => g (θ, r)))
    (hfg : ∀ᵐ r ∂volume, ∀ _hr : r ∈ Ioo a b,
      (fun θ => f (θ, r)) =ᵐ[μ] (fun θ => g (θ, r))) : H = K := by
  have hdiff : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      (H - K) ⟨r, hr.1.le, hr.2.le⟩ ∈ ({0} : Set (Lp E 2 μ)) := by
    filter_upwards [hH, hK, hfg] with r hHr hKr hfgr hr
    obtain ⟨hFL, hHFL⟩ := hHr hr
    obtain ⟨hGL, hKGL⟩ := hKr hr
    change H ⟨r, hr.1.le, hr.2.le⟩ - K ⟨r, hr.1.le, hr.2.le⟩ ∈ ({0} : Set (Lp E 2 μ))
    rw [mem_singleton_iff, sub_eq_zero, hHFL, hKGL]
    exact hFL.toLp_congr hGL (hfgr hr)
  have hall := continuous_interval_mem_closed_of_ae hab (H - K) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro r
  exact sub_eq_zero.mp (mem_singleton_iff.mp (hall r))

/-- Conditional representatives of the same original ambient map on two
radial intervals agree throughout every nondegenerate closed common band. -/
theorem radial_representatives_eq_on_closed_overlap {n q : ℕ}
    {u : Domain n → Ambient q} (c : Domain n)
    {a b A B s t : ℝ} (hst : s < t)
    (has : a ≤ s) (htb : t ≤ b) (hAs : A ≤ s) (htB : t ≤ B)
    (H : C(Icc a b, Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))))
    (K : C(Icc A B, Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))))
    (hH : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)))
    (hK : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo A B,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val))) :
    ∀ r : Icc s t,
      H ⟨r.val, has.trans r.property.1, r.property.2.trans htb⟩ =
        K ⟨r.val, hAs.trans r.property.1, r.property.2.trans htB⟩ := by
  let iH : C(Icc s t, Icc a b) :=
    ⟨fun r => ⟨r.val, has.trans r.property.1, r.property.2.trans htb⟩,
      continuous_subtype_val.subtype_mk _⟩
  let iK : C(Icc s t, Icc A B) :=
    ⟨fun r => ⟨r.val, hAs.trans r.property.1, r.property.2.trans htB⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hH' : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo s t,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        (H.comp iH) ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) := by
    filter_upwards [hH] with r hHr hr
    exact hHr ⟨has.trans_lt hr.1, hr.2.trans_le htb⟩
  have hK' : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo s t,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        (K.comp iK) ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) := by
    filter_upwards [hK] with r hKr hr
    exact hKr ⟨hAs.trans_lt hr.1, hr.2.trans_le htB⟩
  have heq := continuous_Lp_representatives_eq_of_ae_slices
    (f := fun p : sphere (0 : Domain n) 1 × ℝ => u (c + p.2 • p.1.val))
    (g := fun p : sphere (0 : Domain n) 1 × ℝ => u (c + p.2 • p.1.val))
    hst (H.comp iH) (K.comp iK) hH' hK'
      (Eventually.of_forall fun _ _ => Filter.EventuallyEq.rfl)
  intro r
  exact congrArg (fun L => L r) heq

/-- Conditional radial representatives are unchanged by actual ambient a.e.
equality on a ball containing their entire positive radial interval. -/
theorem radial_representatives_eq_of_ae_ambient_ball {n q : ℕ}
    (hn : 0 < n) {u v : Domain n → Ambient q} {c : Domain n}
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R)
    (huv : u =ᵐ[volume.restrict (ball c R)] v)
    (H K : C(Icc a b, Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))))
    (hH : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)))
    (hK : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val))) : H = K := by
  have hpolar := ae_polar_slice_of_ae_ball (a := c) (R := R) huv
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at hpolar
  have hpolar' := (ae_restrict_iff' measurableSet_Ioo).mp hpolar
  apply continuous_Lp_representatives_eq_of_ae_slices
    (f := fun p : sphere (0 : Domain n) 1 × ℝ => u (c + p.2 • p.1.val))
    (g := fun p : sphere (0 : Domain n) 1 × ℝ => v (c + p.2 • p.1.val)) hab H K hH hK
  filter_upwards [hpolar'] with r hr hrI
  exact hr ⟨ha.trans hrI.1, hrI.2.trans hbR⟩

end StratificationTheory
