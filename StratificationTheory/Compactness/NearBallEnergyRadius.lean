module

public import HarmonicMaps.Analysis.BallEnergyAbsoluteContinuity

public section

open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory.Compactness

/-- The actual finite Sobolev energy on an inner ball is approximated from
above by strictly larger concentric balls inside a fixed outer ball. -/
theorem exists_larger_radius_integral_hsNormSq_lt {n q : ℕ} (hn : 0 < n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    {c : Domain n} {s T ε : ℝ} (hs : 0 < s) (hsT : s < T) (hε : 0 < ε)
    (hu : MemW12 (ballDomain c T) u Du) :
    ∃ t : ℝ, s < t ∧ t < T ∧
      (∫ x in ball c t, hsNormSq (Du x)) < (∫ x in ball c s, hsNormSq (Du x)) + ε := by
  have hT : 0 < T := hs.trans hsT
  have hI : IntegrableOn (fun x => hsNormSq (Du x)) (ball c T) := hu.integrable_hsNormSq
  have hAC := absolutelyContinuousOnInterval_integral_ball hn hT.le hI
  have hcOn : ContinuousOn (fun r : ℝ => ∫ x in ball c r, hsNormSq (Du x)) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using hAC.continuousOn
  have hc := hcOn.continuousAt (Icc_mem_nhds hs hsT)
  obtain ⟨d, hd, hdelta⟩ := Metric.continuousAt_iff.mp hc ε hε
  let z := min (d / 2) ((T - s) / 2)
  have hz : 0 < z := lt_min (by positivity) (by positivity)
  let t := s + z
  have hst : s < t := by dsimp only [t]; linarith only [hz]
  have htT : t < T := by
    have h := min_le_right (d / 2) ((T - s) / 2)
    dsimp only [t, z]
    linarith only [h, hsT]
  have htd : dist t s < d := by
    have h := min_le_left (d / 2) ((T - s) / 2)
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hst)]
    dsimp only [t, z]
    linarith only [h, hd]
  refine ⟨t, hst, htT, ?_⟩
  have h := (abs_lt.mp (show |(∫ x in ball c t, hsNormSq (Du x)) -
      (∫ x in ball c s, hsNormSq (Du x))| < ε from by
        simpa only [Real.dist_eq] using hdelta htd)).2
  linarith only [h]

end StratificationTheory.Compactness
