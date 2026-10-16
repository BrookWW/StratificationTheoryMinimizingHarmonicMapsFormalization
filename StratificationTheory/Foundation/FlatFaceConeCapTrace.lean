module

public import StratificationTheory.Foundation.InverseDilationLpTrace

public section
open HarmonicMaps MeasureTheory Set Filter
namespace StratificationTheory

/-- The same literal face-cone extension has a genuine continuous L2 trace
in fixed flat coordinates on every inner subface. The cap class is the
original face class; no homothetic-coordinate trace is assumed. -/
theorem exists_fixed_subface_cone_cap_L2_trace {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (f : Domain n → E) :
    let B : Set (Domain n) := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let U : Set (Domain n) := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-ρ) ρ
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let W : Domain (n + 1) → E := fun y => f (((e y).2 0)⁻¹ • (e y).1)
    MemLp f 2 (volume.restrict B) →
    (∀ r : Icc ρ 1, ∀ x ∈ U, r.val⁻¹ • x ∈ B) ∧
    ∃ H : C(Icc ρ 1, Lp E 2 (volume.restrict U)),
      (∀ r : Icc ρ 1,
        ∃ hr : MemLp (fun x : Domain n =>
            W (e.symm (x, EuclideanSpace.single (0 : Fin 1) r.val))) 2 (volume.restrict U),
          H r = hr.toLp (fun x : Domain n =>
            W (e.symm (x, EuclideanSpace.single (0 : Fin 1) r.val)))) ∧
      (∃ hFU : MemLp f 2 (volume.restrict U), H ⟨1, hρ1.le, le_rfl⟩ = hFU.toLp f) ∧
      (∀ P : E → Prop, (∀ᵐ x ∂volume.restrict B, P (f x)) →
        ∀ r : Icc ρ 1, ∀ᵐ x ∂volume.restrict U, P (H r x)) ∧
      ∀ K : C(Icc ρ 1, Lp E 2 (volume.restrict U)),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo ρ 1,
          ∃ hslice : MemLp (fun x : Domain n =>
              W (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))) 2 (volume.restrict U),
            K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x : Domain n =>
              W (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))) → K = H := by
  intro B U e W hf
  have hB : MeasurableSet B := MeasurableSet.iInter fun i : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable
  have hU : MeasurableSet U := MeasurableSet.iInter fun i : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable
  have hcontain (r : Icc ρ 1) (x : Domain n) (hx : x ∈ U) : r.val⁻¹ • x ∈ B := by
    apply mem_iInter.mpr
    intro i
    have hxi : -ρ < x i ∧ x i < ρ := (mem_iInter.mp hx i)
    have hr : 0 < r.val := hρ.trans_le r.property.1
    have hlo : -r.val < x i := (neg_le_neg r.property.1).trans_lt hxi.1
    have hhi : x i < r.val := hxi.2.trans_le r.property.1
    change (-1 : ℝ) < r.val⁻¹ * x i ∧ r.val⁻¹ * x i < 1
    constructor
    · have h : (-1 : ℝ) < x i / r.val := (lt_div_iff₀ hr).mpr (by simpa only [neg_one_mul] using hlo)
      simpa only [div_eq_mul_inv, mul_comm] using h
    · have h : x i / r.val < 1 := (div_lt_one hr).mpr hhi
      simpa only [div_eq_mul_inv, mul_comm] using h
  obtain ⟨H, hnorm, hend, huniq⟩ :=
    exists_inverse_dilation_L2_trace_on_subset hB hU hf hρ hρ1 hcontain
  have hraw (x : Domain n) (r : ℝ) :
      W (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)) = f (r⁻¹ • x) := by
    simp only [W, ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true]
  refine ⟨hcontain, H, ?_, hend, ?_, ?_⟩
  · simpa only [hraw] using hnorm
  · intro P hP r
    obtain ⟨hL, hEq⟩ := hnorm r
    have hp := ae_inverse_dilation_property_on_subset hB hU f P
      (hρ.trans_le r.property.1).ne' (hcontain r) hP
    rw [hEq]
    filter_upwards [hL.coeFn_toLp, hp] with x hx hpx
    rw [hx]
    exact hpx
  · intro K hK
    apply huniq K
    simpa only [hraw] using hK

end StratificationTheory
