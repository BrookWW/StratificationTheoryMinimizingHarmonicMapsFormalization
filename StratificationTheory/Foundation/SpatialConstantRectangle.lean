module

public import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
public import StratificationTheory.Foundation.CoordinatePiecewiseSobolevData

public section
open HarmonicMaps MeasureTheory Set
open scoped Topology ENNReal BigOperators ContDiff
namespace StratificationTheory

/-- A genuine spatial weak map has the same spatial columns and zero time
column on every finite open time rectangle. -/
theorem memW12_spatial_constant_rectangle {m q : ℕ} (U : OpenDomain m)
    (w : Domain m → Ambient q) (Dw : Domain m → Gradient m q)
    (hw : MemW12 U w Dw) (a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)
    let P : Domain (m + 1) →L[ℝ] Domain m :=
      (ContinuousLinearMap.fst ℝ (Domain m) (Domain 1)).comp e.toContinuousLinearMap
    let Ω : OpenDomain (m + 1) :=
      ⟨{x | P x ∈ U.val ∧ (e x).2 0 ∈ Ioo a b},
        (U.property.preimage P.continuous).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let D := fun (x : Domain (m + 1)) (i : Fin (m + 1)) =>
      Fin.lastCases (0 : Ambient q) (fun j => Dw (P x) j) i
    MemW12 Ω (w ∘ P) D := by
  intro e P Ω D
  have hMP := measurePreserving_inverse_native_rectangle U.property.measurableSet measurableSet_Ioo (J := Ioo a b)
  change MeasurePreserving (fun z : Domain m × ℝ =>
    e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2))
    ((volume.restrict U.val).prod (volume.restrict (Ioo a b))) (volume.restrict Ω.val) at hMP
  have hMap : Measure.map P (volume.restrict Ω.val) =
      ((volume : Measure ℝ) (Ioo a b)) • volume.restrict U.val := by
    rw [← hMP.map_eq, Measure.map_map P.continuous.measurable hMP.measurable]
    have hComp : (P : Domain (m + 1) → Domain m) ∘
        (fun z : Domain m × ℝ => e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2)) = Prod.fst := by
      funext z
      change (e (e.symm _)).1 = _
      rw [e.apply_symm_apply]
    rw [hComp, Measure.map_fst_prod, Measure.restrict_apply_univ]
  have hF : ContDiffOn ℝ ∞ (P : Domain (m + 1) → Domain m) Ω.val := P.contDiff.contDiffOn
  have hDeriv x : fderiv ℝ (P : Domain (m + 1) → Domain m) x = P := P.fderiv
  have hWeak := memW12_smooth_open_domain_pullback hw Ω P hF (fun _ hx => hx.1)
    ‖P‖ (fun x _ => by rw [hDeriv]) (volume (Ioo a b)) (by simp) hMap.le
  have hColumns (x : Domain (m + 1)) (i : Fin (m + 1)) :
      (∑ j : Fin m, (fderiv ℝ (P : Domain (m + 1) → Domain m) x
        (EuclideanSpace.single i 1)) j • Dw (P x) j) = D x i := by
    rw [hDeriv]
    have hCoord (j : Fin m) : (P (EuclideanSpace.single i 1)) j =
        if j.castSucc = i then 1 else 0 := by
      change (EuclideanSpace.single i (1 : ℝ)) j.castSucc = _
      rw [PiLp.single_apply]
    simp only [hCoord]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.castSucc_ne_last, ite_false, zero_smul, Finset.sum_const_zero, D, Fin.lastCases_last]
    · simp only [Fin.castSucc_inj, D, Fin.lastCases_castSucc]
      simp
  convert hWeak using 1
  funext x i
  exact (hColumns x i).symm

end StratificationTheory
