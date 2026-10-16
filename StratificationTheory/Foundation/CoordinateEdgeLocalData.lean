module

public import StratificationTheory.Foundation.CoordinateNormalLineGeometry
public import StratificationTheory.Foundation.IntervalSobolevTranslation

/-!
# Actual local edge data from the original coordinate line

Translation of the original coordinate line identifies its finite weak
data with the literal local edge parameter. The two closed endpoint values
are the given original raw vertex values, and the derivative is unchanged.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original full-line qualifications at an edge and its two raw vertices
give all finite data of that same local edge. The local regularity and
increments are derived by actual interval translation. -/
theorem coordinate_edge_original_local_data {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (y : Domain (n + 1))
    {a b ε : ℝ} (hε : 0 < ε)
    {u R : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    {N : Set (Ambient q)} :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := (e (Q.symm y)).1
    let line := fun t => Q (e.symm (β, EuclideanSpace.single (0 : Fin 1) t))
    let F := fun s => R (y + s • v)
    let f := fun s => u (y + s • v)
    let g := fun s => Du (y + s • v) j
    a ≤ y j → y j + ε ≤ b →
    MemLp (u ∘ line) 2 (volume.restrict (Ioo a b)) →
    MemLp (fun t => Du (line t) j) 2 (volume.restrict (Ioo a b)) →
    (R ∘ line) =ᵐ[volume.restrict (Ioo a b)] (u ∘ line) →
    (∀ t ∈ Icc a b, R (line t) ∈ N) →
    (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      R (line t) - R (line s) = ∫ r in s..t, Du (line r) j) →
    R y = u y → R (y + ε • v) = u (y + ε • v) →
    MemLp f 2 (volume.restrict (Ioo (0 : ℝ) ε)) ∧
      MemLp g 2 (volume.restrict (Ioo (0 : ℝ) ε)) ∧
      AbsolutelyContinuousOnInterval F 0 ε ∧
      F =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f ∧
      (∀ s ∈ Icc (0 : ℝ) ε, F s ∈ N) ∧
      (∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ε), f s ∈ N) ∧
      (∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
        F t - F s = ∫ r in s..t, g r) ∧
      F 0 = u y ∧ F ε = u (y + ε • v) := by
  intro Q e j v β line F f g ha hb hu hDu hAE hN hinc hraw₀ hraw₁
  have hline (s : ℝ) : line (y j + s) = y + s • v := by
    have h := coordinate_line_eq_add_normal p y (y j + s)
    change line (y j + s) = y + (y j + s - y j) • v at h
    simpa only [add_sub_cancel_left] using h
  have hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) ε)) := by
    have h := memLp_translated_subinterval ha hb hu
    simpa only [Function.comp_def, hline] using h
  have hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) ε)) := by
    have h := memLp_translated_subinterval ha hb hDu
    simpa only [hline] using h
  have hFae : F =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f := by
    have h := ae_translated_subinterval ha hb hAE
    change ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ε), R (y + s • v) = u (y + s • v)
    simpa only [Function.comp_def, hline] using h
  have hFinc : ∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
      F t - F s = ∫ r in s..t, g r := by
    have h := integral_increments_translated_subinterval ha hb hinc
    simpa only [hline] using h
  have hFAC : AbsolutelyContinuousOnInterval F 0 ε :=
    absolutelyContinuousOnInterval_of_integral_increments hε.le hg hFinc
  have hFN : ∀ s ∈ Icc (0 : ℝ) ε, F s ∈ N := by
    intro s hs
    have hs' : y j + s ∈ Icc a b :=
      ⟨by linarith only [ha, hs.1], by linarith only [hb, hs.2]⟩
    simpa only [hline] using hN (y j + s) hs'
  have hfN : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ε), f s ∈ N := by
    filter_upwards [hFae, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    rw [← hs]
    exact hFN s ⟨hsI.1.le, hsI.2.le⟩
  refine ⟨hf, hg, hFAC, hFae, hFN, hfN, hFinc, ?_, hraw₁⟩
  simpa only [F, zero_smul, add_zero] using hraw₀

end StratificationTheory
