module

public import StratificationTheory.Interpolation.OriginalGridNearLevelChannels
public import StratificationTheory.Foundation.ScaledGridCubeEdges
public import StratificationTheory.Foundation.CubicalNearLevelLocalTube
public import StratificationTheory.Foundation.OriginalCoordinateLineChannels

/-! # Original cubical edge complex and tube on one selected radius -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

private theorem real_tube_uniform_scale {ε K A D X Y : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hX : 0 ≤ X) (hAX : X ≤ K * A) (hDY : Y ≤ K * D) :
    Y / ε + Real.sqrt (2 * Y * X) ≤ K * (D / ε + Real.sqrt (2 * D * A)) := by
  have hProd : 2 * Y * X ≤ K ^ 2 * (2 * D * A) := by
    calc
      _ ≤ 2 * (K * D) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDY (by norm_num)) hX
      _ ≤ 2 * (K * D) * (K * A) :=
        mul_le_mul_of_nonneg_left hAX (mul_nonneg (by norm_num) (mul_nonneg hK hD))
      _ = _ := by ring
  calc
    _ ≤ (K * D) / ε + Real.sqrt (K ^ 2 * (2 * D * A)) :=
      add_le_add (div_le_div_of_nonneg_right hDY hε.le) (Real.sqrt_le_sqrt hProd)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
      ring

/-- Original selected one-face channels produce a single radius with the
correct near-level width gain for every actual edge of every contained
full cubical cell intersecting that level. All edge shifts and their closed
carrier inclusion are produced from the actual lattice generators. -/
theorem original_selected_grid_joint_near_level_edge_complex {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε a b : ℝ} (hε : 0 < ε) (hab : a < b) (count : ℕ)
    (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let I := Fin (n + 2) × (Fin (n + 1) → Bool)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let C := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Eline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Eraw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let Dline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Draw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
        ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    let B := 6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * (Fintype.card I : ℝ≥0∞) * c
    let er := fun (i : I) (z : L) => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) i.1‖ ^ 2 +
        ‖Dw 1 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) i.1‖ ^ 2
    let dr := fun (i : I) (z : L) => ∫ s in Ioo (0 : ℝ) ε,
      ‖w 0 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) -
        w 1 (y z + s • EuclideanSpace.single i.1 (1 : ℝ))‖ ^ 2
    let vertex := fun i : I =>
      (WithLp.toLp 2 (fun j : Fin (n + 1) => if i.2 j then ε else 0) : Domain (n + 1))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    (∀ k, (∑' z : L, Eline k z) ≤ c * ENNReal.ofReal A₀) →
    (∀ k, (∑' z : L, Dline k z) ≤ c * ENNReal.ofReal D₀) →
    ∀ energy : ℝ → ℝ≥0∞,
    AEMeasurable energy (volume.restrict (Ioo a b)) →
    (∫⁻ r in Ioo a b, energy r) ≠ ⊤ →
    ∀ P : ℝ → Prop, (∀ᵐ r ∂volume.restrict (Ioo a b), P r) →
    ∃ (shift : I → L) (r : ℝ),
      r ∈ Ioo a b ∧ P r ∧
      energy r ≤ 3 * (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ s in Ioo a b, energy s ∧
      (∀ (i : I) (z : L) (s : ℝ),
        y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
          y z + cubicalSignedFaceIsometry (n + 1) i.1 true
            (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s))) ∧
      (∀ (i : I) (z : L) (s : ℝ), s ∈ Icc (0 : ℝ) ε → ∀ j,
        (y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ)) j - (y z) j ∈ Icc (0 : ℝ) ε) ∧
      ∀ z : L,
        (∀ x : Domain (n + 2), (∀ j, x j - (y z) j ∈ Icc (0 : ℝ) ε) →
          x ∈ ball (0 : Domain (n + 2)) ((n : ℝ) + 3)) →
        (∃ x : Domain (n + 2), (∀ j, x j - (y z) j ∈ Icc (0 : ℝ) ε) ∧ ‖WithLp.ofLp x‖ = r) →
        (∑ i : I, (dr i (z + shift i) / ε + Real.sqrt (2 * dr i (z + shift i) * er i (z + shift i)))) ≤
          (Fintype.card I : ℝ) * B.toReal * (D₀ / ε + Real.sqrt (2 * D₀ * A₀)) := by
  intro grid L I y C Eraw Draw Eline Dline A₀ D₀ c B er dr vertex e hSelectE hSelectD energy hEnergy hEnergyFinite P hP
  obtain ⟨shift, hShift⟩ := exists_scaled_grid_cube_edge_offsets hε offset
  obtain ⟨r, hr, hPr, hE, hAE, hDE⟩ := original_selected_grid_joint_near_level_channels
    (I := I) w Dw hε hab count offset shift (fun i => i.1) hSelectE hSelectD energy hEnergy hEnergyFinite P hP
  let En := fun i : I => Eline i.1
  let Dn := fun i : I => Dline i.1
  let near := fun (weight : I → L → ℝ≥0∞) => ∑' z : L,
    (Icc (‖WithLp.ofLp (y z)‖ - ε) (‖WithLp.ofLp (y z)‖ + ε)).indicator
      (fun _ : ℝ => ∑ i : I, weight i (z + shift i)) r
  have hAN : near En ≤ B * ENNReal.ofReal A₀ := by simpa only [near, En, B, c, Eline, Eraw, y, C, A₀, mul_assoc] using hAE
  have hDN : near Dn ≤ B * ENNReal.ofReal D₀ := by simpa only [near, Dn, B, c, Dline, Draw, y, C, D₀, mul_assoc] using hDE
  have hcFinite : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hε _)).ne'))
      (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top)
  have hBFinite : B ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
          (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne')) (by finiteness)) hcFinite
  have hAFinite : near En ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hBFinite ENNReal.ofReal_ne_top) hAN
  have hDFinite : near Dn ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hBFinite ENNReal.ofReal_ne_top) hDN
  have hA₀ : 0 ≤ A₀ := add_nonneg
    (integral_nonneg fun _ => hsNormSq_nonneg _) (integral_nonneg fun _ => hsNormSq_nonneg _)
  have hD₀ : 0 ≤ D₀ := integral_nonneg fun _ => sq_nonneg _
  have hAR : (near En).toReal ≤ B.toReal * A₀ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hBFinite ENNReal.ofReal_ne_top) hAN
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA₀] using h
  have hDR : (near Dn).toReal ≤ B.toReal * D₀ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hBFinite ENNReal.ofReal_ne_top) hDN
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD₀] using h
  refine ⟨shift, r, hr, hPr, hE, fun i z s => (hShift i z s).1,
    fun i z s hs => (hShift i z s).2 hs, ?_⟩
  intro z hCell hMeet
  have hImage (i : I) : ∀ s ∈ Ioo (0 : ℝ) ε,
      y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) ∈
        ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
    intro s hs
    exact hCell _ ((hShift i z s).2 ⟨hs.1.le, hs.2.le⟩)
  have hANative (i : I) : ENNReal.ofReal (er i (z + shift i)) ≤ En i (z + shift i) :=
    original_real_edge_combined_energy_le_native_channel (y (z + shift i)) i.1 Dw (hImage i)
  have hDNative (i : I) : ENNReal.ofReal (dr i (z + shift i)) ≤ Dn i (z + shift i) :=
    original_real_edge_discrepancy_le_native_channel (y (z + shift i)) i.1 w (hImage i)
  have hTube := local_edge_tube_le_cubical_near_level_sums hε y shift En Dn hAFinite hDFinite z
    (fun i => er i (z + shift i)) (fun i => dr i (z + shift i))
    (fun _ => integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun _ => integral_nonneg fun _ => sq_nonneg _) hANative hDNative hMeet
  have hScale := real_tube_uniform_scale hε ENNReal.toReal_nonneg hD₀
    ENNReal.toReal_nonneg hAR hDR
  exact hTube.trans ((mul_le_mul_of_nonneg_left hScale (Nat.cast_nonneg _)).trans_eq (by ring))

end StratificationTheory
