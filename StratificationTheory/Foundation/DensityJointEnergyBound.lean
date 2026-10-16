module

public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.Foundation.EnergyRadiusContinuity
public import StratificationTheory.Foundation.PositiveRadiusLimits
public import Mathlib.Topology.Order.LiminfLimsup

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- Actual whole-sequence ball energy convergence controls the joint moving
center density limsup. Finite upper bounds and nonnegative lower bounds are
produced before the real limsup and the two successive radius limits. -/
theorem density_joint_upper_bound_of_ball_energy_convergence {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hMinimizer : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hv : MemW12Loc Ω v Dv) (hTv : TakesValuesIn N Ω v)
    (hMinV : IsLocallyEnergyMinimizing N Ω v Dv)
    (hEnergyConv : ∀ (c : Domain n) (r : ℝ), 0 < r → closedBall c r ⊆ Ω.val →
      Tendsto (fun k => ∫ x in ball c r, hsNormSq (Du k x)) atTop
        (𝓝 (∫ x in ball c r, hsNormSq (Dv x))))
    (a : Ω.val) (y : ℕ → Ω.val)
    (hy : Tendsto (fun k => (y k).val) atTop (𝓝 a.val)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      density hn (hMinimizer k) (hu k) (hTarget k) (y k) ≤ density hn hMinV hv hTv a + ε) ∧
    Filter.limsup (fun k => density hn (hMinimizer k) (hu k) (hTarget k) (y k)) atTop ≤
      density hn hMinV hv hTv a := by
  let θ : ℕ → ℝ := fun k => density hn (hMinimizer k) (hu k) (hTarget k) (y k)
  have hNonnegative (k : ℕ) : 0 ≤ θ k := density_nonneg hn (hMinimizer k) (hu k) (hTarget k) (y k)
  have hCobounded : atTop.IsCoboundedUnder (· ≤ ·) θ := isCoboundedUnder_le_of_le atTop hNonnegative
  obtain ⟨R, hR, hOuter⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds a.property)
  have hDistance : Tendsto (fun k => dist (y k).val a.val) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hy
  have hCompare (r s : PositiveRadius) (hrs : r.val < s.val) (hsR : s.val < R) :
      (∀ᶠ k in atTop, θ k ≤ r.val ^ (2 - (n : ℤ)) * ∫ x in ball a.val s.val, hsNormSq (Du k x)) ∧
      Tendsto (fun k => r.val ^ (2 - (n : ℤ)) * ∫ x in ball a.val s.val, hsNormSq (Du k x))
        atTop (𝓝 (r.val ^ (2 - (n : ℤ)) * ∫ x in ball a.val s.val, hsNormSq (Dv x))) := by
    have hsClosed : closedBall a.val s.val ⊆ Ω.val :=
      (closedBall_subset_closedBall hsR.le).trans hOuter
    refine ⟨?_, (hEnergyConv a.val s.val s.property hsClosed).const_mul _⟩
    filter_upwards [hDistance.eventually (gt_mem_nhds (sub_pos.mpr hrs))] with k hk
    have hBall : r.val + dist (y k).val a.val ≤ s.val := by linarith
    have hkClosed : closedBall (y k).val r.val ⊆ Ω.val :=
      (closedBall_subset_closedBall' hBall).trans hsClosed
    exact (density_le_normalizedEnergy_toReal hn (hMinimizer k) (hu k) (hTarget k) (y k) r hkClosed).trans
      ((hu k).normalizedEnergy_toReal_le_ball_integral (y k).val a.val r s hBall hsClosed)
  have hBounded : atTop.IsBoundedUnder (· ≤ ·) θ := by
    obtain ⟨hCompare₀, hConv₀⟩ := hCompare ⟨R / 4, by positivity⟩ ⟨R / 2, by positivity⟩
      (by simp only; linarith) (by simp only; linarith)
    exact hConv₀.isBoundedUnder_le.mono_le hCompare₀
  have hFixedRadius (r : PositiveRadius) (hrR : r.val < R) :
      Filter.limsup θ atTop ≤ (normalizedEnergy Dv a.val r).toReal := by
    have hInt : IntegrableOn (fun x => hsNormSq (Dv x)) (ball a.val r.val) :=
      hv.integrable_hsNormSq_ball ((closedBall_subset_closedBall hrR.le).trans hOuter)
    have hVal : Tendsto (Subtype.val : PositiveRadius → ℝ) atBot (𝓝 (0 : ℝ)) :=
      positiveRadius_val_tendsto_zero
    have hRadius : Tendsto (fun s : PositiveRadius => r.val + s.val) atBot (𝓝 r.val) := by
      simpa only [add_zero] using tendsto_const_nhds.add hVal
    have hContinuous := hv.continuousAt_dirichletEnergy_toReal_ball_radius (by omega : 0 < n)
      r.property hrR hOuter
    have hOuterConv : Tendsto (fun s : PositiveRadius => r.val ^ (2 - (n : ℤ)) *
        (dirichletEnergy Dv (ball a.val (r.val + s.val))).toReal) atBot
        (𝓝 ((normalizedEnergy Dv a.val r).toReal)) := by
      have hh := (hContinuous.tendsto.comp hRadius).const_mul (r.val ^ (2 - (n : ℤ)))
      simpa only [Function.comp_def, normalizedEnergy_toReal hInt, dirichletEnergy_toReal hInt] using hh
    apply ge_of_tendsto hOuterConv
    filter_upwards [eventually_le_atBot (⟨(R - r.val) / 2, half_pos (sub_pos.mpr hrR)⟩ : PositiveRadius)] with s hs
    have hsR : r.val + s.val < R := by
      change s.val ≤ (R - r.val) / 2 at hs
      linarith [s.property]
    let outer : PositiveRadius := ⟨r.val + s.val, add_pos r.property s.property⟩
    obtain ⟨hCompareS, hConvS⟩ := hCompare r outer (by dsimp only [outer]; linarith [s.property]) hsR
    have hLe := limsup_le_limsup hCompareS hCobounded hConvS.isBoundedUnder_le
    rw [hConvS.limsup_eq] at hLe
    have hIntOuter := hv.integrable_hsNormSq_ball ((closedBall_subset_closedBall hsR.le).trans hOuter)
    simpa only [dirichletEnergy_toReal hIntOuter] using hLe
  have hLimsup : Filter.limsup θ atTop ≤ density hn hMinV hv hTv a := by
    apply ge_of_tendsto (normalizedEnergy_tendsto_density_atBot hn hMinV hv hTv a)
    filter_upwards [eventually_le_atBot (⟨R / 2, half_pos hR⟩ : PositiveRadius)] with r hr
    exact hFixedRadius r (lt_of_le_of_lt hr (half_lt_self hR))
  refine ⟨?_, hLimsup⟩
  intro ε hε
  have hEvent := (limsup_le_iff hCobounded hBounded).mp hLimsup
    (density hn hMinV hv hTv a + ε) (by linarith)
  exact hEvent.mono fun _ hk => hk.le

end StratificationTheory
