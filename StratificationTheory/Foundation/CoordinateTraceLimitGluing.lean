module

public import StratificationTheory.Foundation.CoordinateRectangleTrace
public import StratificationTheory.Foundation.ContinuousTraceEndpoint
public import StratificationTheory.Foundation.CoordinateTraceWeakGluing

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Genuine one-sided limits of the original raw slices produce matching
traces and full weak gluing of the same original piecewise pair. -/
theorem memW12_coordinate_piecewise_of_common_raw_L2_limit {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (u v : Domain (n + 1) → Ambient q) (Du Dv : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
      ((ContinuousLinearMap.snd ℝ (Domain n) (Domain 1)).comp e.toContinuousLinearMap)
    let Ω : ℝ → ℝ → OpenDomain (n + 1) := fun d f =>
      ⟨{y | (e y).1 ∈ U.val ∧ T y ∈ Ioo d f},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage T.continuous)⟩
    MemW12 (Ω a b) u Du → MemW12 (Ω b c) v Dv →
    ∀ g : Domain n → Ambient q, ∀ hg : MemLp g 2 (volume.restrict U.val),
      Tendsto (fun t => eLpNorm (fun x : Domain n =>
        u (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) - g x) 2 (volume.restrict U.val))
          (𝓝[<] b) (𝓝 0) →
      Tendsto (fun t => eLpNorm (fun x : Domain n =>
        v (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) - g x) 2 (volume.restrict U.val))
          (𝓝[>] b) (𝓝 0) →
      let f : Domain (n + 1) → Ambient q := fun y => if T y < b then u y else v y
      let Df : Domain (n + 1) → Gradient (n + 1) q := fun y i => if T y < b then Du y i else Dv y i
      MemW12 (Ω a c) f Df ∧
      (∫ y in (Ω a c).val, hsNormSq (Df y)) =
        (∫ y in (Ω a b).val, hsNormSq (Du y)) + (∫ y in (Ω b c).val, hsNormSq (Dv y)) ∧
      ∃ J : C(Icc a c, Lp (Ambient q) 2 (volume.restrict U.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hs : MemLp (fun x => f (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2
              (volume.restrict U.val),
            J ⟨t, ht.1.le, ht.2.le⟩ =
              hs.toLp (fun x => f (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        J ⟨b, hab.le, hbc.le⟩ = hg.toLp g := by
  intro e T Ω hu hv g hg hleft hright f Df
  obtain ⟨H, hH, _hHunique⟩ := exists_unique_L2_trace_of_memW12_rectangle (n := n) (q := q) U (a := a) (b := b) hab (u := u) (Du := Du) hu
  obtain ⟨K, hK, _hKunique⟩ := exists_unique_L2_trace_of_memW12_rectangle (n := n) (q := q) U (a := b) (b := c) hbc (u := v) (Du := Dv) hv
  have hHend : H ⟨b, hab.le, le_rfl⟩ = hg.toLp g :=
    continuous_L2_trace_right_endpoint_of_raw_limit (volume.restrict U.val) hab H
      (f := fun p : Domain n × ℝ => u (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      hH (g := g) hg hleft
  have hKend : K ⟨b, le_rfl, hbc.le⟩ = hg.toLp g :=
    continuous_L2_trace_left_endpoint_of_raw_limit (volume.restrict U.val) hbc K
      (f := fun p : Domain n × ℝ => v (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      hK (g := g) hg hright
  obtain ⟨hW, hE, J, hJL, _hJR, hJraw⟩ :=
    memW12_coordinate_piecewise_of_matching_L2_traces (n := n) (q := q) U (a := a) (b := b) (c := c) hab hbc u v Du Dv hu hv H K hH hK
      (hHend.trans hKend.symm)
  exact ⟨hW, hE, J, hJraw, (hJL ⟨b, hab.le, le_rfl⟩).trans hHend⟩

end StratificationTheory
