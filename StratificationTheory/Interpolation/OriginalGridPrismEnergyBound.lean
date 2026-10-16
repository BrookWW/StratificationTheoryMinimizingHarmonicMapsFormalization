module
public import StratificationTheory.Foundation.SortedCellPrismEnergySum
public import StratificationTheory.Foundation.OriginalPhysicalCellWeightedEnergySum
public import StratificationTheory.Foundation.OriginalPhysicalCellLineEnergySum
public import StratificationTheory.Foundation.PrismWeightedEdgeBase
public import StratificationTheory.Foundation.PrismWeightedEnergyRecurrence

/-!
# The actual terminal-rank prism energy from one original selected grid

The literal physical energies of one actual prism family obey their original
cellwise inequalities. Actual facet incidence, original horizontal energies
at every rank, and the two original edge channels give the full terminal
energy budget. Its coefficient depends only on the ambient dimension.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Genuine physical-cell base and coning inequalities, supplied by an
actual constructed family on the same original selected grid, imply the
terminal-rank coupled energy bound and finiteness of its complete cell sum. -/
theorem original_selected_grid_prism_total_energy_bound {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε : ℝ} (hε : 0 < ε) (offset : Fin (n + 2) → ℝ) :
    let J := (r : Fin (n + 3)) × (Fin r.val ↪ Fin (n + 2))
    let count : ℕ := Fintype.card J
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let C := fun r => ⋂ k : Fin r, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    (∀ j : J, (∑' z : L, ∫⁻ t in C j.1.val,
      Eraw (y z + ∑ k : Fin j.1.val, t k • EuclideanSpace.single (j.2 k) (1 : ℝ))) ≤
        2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
          ((count : ℝ≥0∞) * ENNReal.ofReal (ε ^ j.1.val)) * ENNReal.ofReal A₀) →
    (∀ normal : Fin (n + 2), (∑' z : L, ∫⁻ t in C 1,
      Draw (y z + t 0 • EuclideanSpace.single normal (1 : ℝ))) ≤
        2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
          ((count : ℝ≥0∞) * ENNReal.ofReal ε) * ENNReal.ofReal D₀) →
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin (n + 2))}
    let axes := fun (r : ℕ) (p : Cell r) => p.val.val.1
    let origin := fun (r : ℕ) (p : Cell r) => p.val.val.2
    let B := fun r : ℕ => ⋂ i : Fin r, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let P := fun r : ℕ => ⋂ i : Fin r, (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) ε
    let originalEnergy := fun (r : ℕ) (p : Cell r) => ∑ l : Fin 2, ∫ x in P r,
      hsNormSq (fun i : Fin r => Dw l (origin r p +
        ∑ j : Fin r, x j • EuclideanSpace.single (axes r p j) (1 : ℝ)) (axes r p i))
    let linePoint := fun (p : Cell 1) (s : ℝ) => origin 1 p +
      ∑ j : Fin 1, (EuclideanSpace.single (0 : Fin 1) s) j • EuclideanSpace.single (axes 1 p j) (1 : ℝ)
    let lineA := fun p : Cell 1 => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (linePoint p s) (axes 1 p 0)‖ ^ 2 + ‖Dw 1 (linePoint p s) (axes 1 p 0)‖ ^ 2
    let lineD := fun p : Cell 1 => ∫ s in Ioo (0 : ℝ) ε, ‖w 0 (linePoint p s) - w 1 (linePoint p s)‖ ^ 2
    ∀ (DV : (r : ℕ) → Cell r → Domain (r + 1) → Gradient (r + 1) q)
      (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r),
    let energy := fun (r : ℕ) (p : Cell r) =>
      (ε / 2) ^ ((r : ℤ) - 1) * ∫ x in B (r + 1), hsNormSq (DV r p x)
    (∀ (r : ℕ) (p : Cell (r + 2)) (i : Fin (r + 2)) (side : Bool),
      axes (r + 1) (child (r + 1) p i side) = i.succAboveEmb.trans (axes (r + 2) p)) →
    (∀ (r : ℕ) (p : Cell (r + 2)) (i : Fin (r + 2)) (side : Bool),
      origin (r + 1) (child (r + 1) p i side) = origin (r + 2) p +
        (if side then ε else 0) • EuclideanSpace.single (axes (r + 2) p i) (1 : ℝ)) →
    (∀ p : Cell 1, energy 1 p ≤ (ε / 2) * lineA p + ε⁻¹ * lineD p) →
    (∀ r : ℕ, 1 ≤ r → ∀ p : Cell (r + 1), energy (r + 1) p ≤
      (((r : ℝ) + 2) / (r : ℝ)) * (ε / 2) *
        (originalEnergy (r + 1) p + ∑ i : Fin (r + 1), ∑ side : Bool, energy r (child r p i side))) →
    let K : ℝ≥0∞ := 4 * (count : ℝ≥0∞) * (count : ℝ≥0∞) *
      (6 * ((n + 3 : ℕ) : ℝ≥0∞)) ^ (n + 1)
    0 < K ∧ K ≠ ⊤ ∧
      (∑' p : Cell (n + 2), ENNReal.ofReal (energy (n + 2) p)) ≤
        K * (ENNReal.ofReal ε * ENNReal.ofReal A₀ +
          (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal D₀) ∧
      (∑' p : Cell (n + 2), ENNReal.ofReal (energy (n + 2) p)) ≠ ⊤ := by
  classical
  intro J count grid L y C Eraw Draw A₀ D₀ hSelectE hSelectD Cell axes origin B P originalEnergy
    linePoint lineA lineD DV child energy hAxes hOrigin hBase hStep K
  let t : ℝ≥0∞ := ENNReal.ofReal ε
  let G : ℝ≥0∞ := 2 * (count : ℝ≥0∞) * (count : ℝ≥0∞)
  let M : ℝ≥0∞ := 6 * ((n + 3 : ℕ) : ℝ≥0∞)
  let total := fun j : ℕ => ∑' p : Cell (j + 1), ENNReal.ofReal (energy (j + 1) p)
  let horizontal := fun j : ℕ => ∑' p : Cell (j + 2), ENNReal.ofReal (originalEnergy (j + 2) p)
  have ht₀ : t ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have htFinite : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact_mod_cast (show 1 ≤ 6 * (n + 3) by omega)
  have hCM : (3 : ℝ≥0∞) * (2 * ((n + 2 : ℕ) : ℝ≥0∞) + 1) ≤ M := by
    dsimp only [M]
    exact_mod_cast (show 3 * (2 * (n + 2) + 1) ≤ 6 * (n + 3) by omega)
  have hEnergyNonneg (r : ℕ) (p : Cell r) : 0 ≤ energy r p :=
    mul_nonneg (le_of_lt (zpow_pos (div_pos hε (by norm_num)) _))
      (integral_nonneg fun _ => hsNormSq_nonneg _)
  have hOriginalNonneg (r : ℕ) (p : Cell r) : 0 ≤ originalEnergy r p :=
    Finset.sum_nonneg fun l _ => integral_nonneg fun _ => hsNormSq_nonneg _
  have hLineA (p : Cell 1) : 0 ≤ lineA p := integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hLineD (p : Cell 1) : 0 ≤ lineD p := integral_nonneg fun _ => sq_nonneg _
  have hRankSelect {r : ℕ} (hr : r ≤ n + 2) (coord : Fin r ↪ Fin (n + 2)) :=
    hSelectE (⟨⟨r, by omega⟩, coord⟩ : J)
  have hHorizontal : ∀ j < n + 1, t ^ (n + 1 - j) * horizontal j ≤ G * t * ENNReal.ofReal A₀ := by
    intro j hj
    have hr : j + 2 ≤ n + 2 := by omega
    have h := original_physical_cell_weighted_energy_tsum_le hr Dw hε count offset (hRankSelect hr)
    simpa only [horizontal, originalEnergy, P, G, count, J, ENNReal.ofReal_pow hε.le,
      show n + 2 - (j + 2) + 1 = n + 1 - j by omega] using h
  have hRankOne (coord : Fin 1 ↪ Fin (n + 2)) :
      (∑' z : L, ∫⁻ s in C 1, Eraw (y z + s 0 • EuclideanSpace.single (coord 0) (1 : ℝ))) ≤
        2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * t) * ENNReal.ofReal A₀ := by
    have h := hRankSelect (r := 1) (by omega) coord
    simpa only [Fin.sum_univ_one, pow_one] using h
  have hCard : (Fintype.card (Fin 1 ↪ Fin (n + 2)) : ℝ≥0∞) ≤ (count : ℝ≥0∞) := by
    exact_mod_cast coordinate_embedding_card_le_all_rank_count (show 1 ≤ n + 2 by omega)
  have hASum : (∑' p : Cell 1, ENNReal.ofReal (lineA p)) ≤ G * (t ^ (n + 2))⁻¹ * t * ENNReal.ofReal A₀ := by
    have h := original_physical_cell_line_energy_tsum_le_native_channels Dw hε count offset hRankOne
    calc
      _ ≤ (Fintype.card (Fin 1 ↪ Fin (n + 2)) : ℝ≥0∞) *
          (2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * t) * ENNReal.ofReal A₀) := by
        simpa only [lineA, linePoint, axes, origin, Fin.sum_univ_one, PiLp.single_apply, ite_true] using h
      _ = 2 * (count : ℝ≥0∞) * (Fintype.card (Fin 1 ↪ Fin (n + 2)) : ℝ≥0∞) *
          (t ^ (n + 2))⁻¹ * t * ENNReal.ofReal A₀ := by
        rw [ENNReal.ofReal_pow hε.le]
        ac_rfl
      _ ≤ _ := by dsimp only [G]; gcongr
  have hDSum : (∑' p : Cell 1, ENNReal.ofReal (lineD p)) ≤ G * (t ^ (n + 2))⁻¹ * t * ENNReal.ofReal D₀ := by
    have h := original_physical_cell_discrepancy_tsum_le_native_channels w hε count offset (fun coord => hSelectD (coord 0))
    calc
      _ ≤ (Fintype.card (Fin 1 ↪ Fin (n + 2)) : ℝ≥0∞) *
          (2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * t) * ENNReal.ofReal D₀) := by
        simpa only [lineD, linePoint, axes, origin, Fin.sum_univ_one, PiLp.single_apply, ite_true] using h
      _ = 2 * (count : ℝ≥0∞) * (Fintype.card (Fin 1 ↪ Fin (n + 2)) : ℝ≥0∞) *
          (t ^ (n + 2))⁻¹ * t * ENNReal.ofReal D₀ := by
        rw [ENNReal.ofReal_pow hε.le]
        ac_rfl
      _ ≤ _ := by dsimp only [G]; gcongr
  have hBaseEnnr (p : Cell 1) : ENNReal.ofReal (energy 1 p) ≤
      t * ENNReal.ofReal (lineA p) + t⁻¹ * ENNReal.ofReal (lineD p) := by
    have h := ENNReal.ofReal_le_ofReal (hBase p)
    rw [ENNReal.ofReal_add (mul_nonneg (by positivity) (hLineA p)) (mul_nonneg (by positivity) (hLineD p)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ ε / 2), ENNReal.ofReal_mul (by positivity : 0 ≤ ε⁻¹),
      ENNReal.ofReal_inv_of_pos hε] at h
    exact h.trans (add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : ε / 2 ≤ ε)) _) le_rfl)
  have hBaseWeighted : t ^ (n + 1) * total 0 ≤ G * (t * ENNReal.ofReal A₀ + t⁻¹ * ENNReal.ofReal D₀) :=
    weighted_original_edge_energy_base n t ht₀ htFinite (fun p : Cell 1 => ENNReal.ofReal (energy 1 p))
      (fun p => ENNReal.ofReal (lineA p)) (fun p => ENNReal.ofReal (lineD p))
      G (ENNReal.ofReal A₀) (ENNReal.ofReal D₀) hASum hDSum hBaseEnnr
  have hPointStep (j : ℕ) (p : Cell (j + 2)) : ENNReal.ofReal (energy (j + 2) p) ≤
      (3 * t) * (ENNReal.ofReal (originalEnergy (j + 2) p) +
        ∑ i : Fin (j + 2), ∑ side : Bool, ENNReal.ofReal (energy (j + 1) (child (j + 1) p i side))) := by
    have hDim : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + 1 by omega)
    have hFactor : ((((j + 1 : ℕ) : ℝ) + 2) / ((j + 1 : ℕ) : ℝ)) ≤ 3 :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))).mpr (by linarith)
    have hSumNonneg : 0 ≤ originalEnergy (j + 2) p +
        ∑ i : Fin (j + 2), ∑ side : Bool, energy (j + 1) (child (j + 1) p i side) :=
      add_nonneg (hOriginalNonneg _ _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun side _ => hEnergyNonneg _ _)
    have hC : ((((j + 1 : ℕ) : ℝ) + 2) / ((j + 1 : ℕ) : ℝ)) * (ε / 2) ≤ 3 * ε := by
      exact (mul_le_mul_of_nonneg_right hFactor (by positivity)).trans (by linarith)
    have hReal := (hStep (j + 1) (by omega) p).trans (mul_le_mul_of_nonneg_right hC hSumNonneg)
    have h := ofReal_finite_prism_energy_bound
      (fun a : Fin (j + 2) × Bool => energy (j + 1) (child (j + 1) p a.1 a.2))
      (by positivity : 0 ≤ 3 * ε) (hOriginalNonneg _ _) (fun _ => hEnergyNonneg _ _)
      (by simpa only [Fintype.sum_prod_type] using hReal)
    simpa only [Fintype.sum_prod_type, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat] using h
  have hTotalStep (j : ℕ) : total (j + 1) ≤ (3 * t) *
      (horizontal j + (2 * ((n + 2 : ℕ) : ℝ≥0∞)) * total j) := by
    exact tsum_sorted_physical_prism_energy_recurrence grid offset ε (child (j + 1))
      (hAxes j) (hOrigin j) (fun p => ENNReal.ofReal (energy (j + 2) p))
      (fun p => ENNReal.ofReal (originalEnergy (j + 2) p))
      (fun p => ENNReal.ofReal (energy (j + 1) p)) (3 * t) (hPointStep j)
  have hBound := weighted_prism_energy_recurrence_from_grid_budget t 3
    (2 * ((n + 2 : ℕ) : ℝ≥0∞)) M G (ENNReal.ofReal A₀) (ENNReal.ofReal D₀)
    hM hCM total horizontal (n + 1) hBaseWeighted hHorizontal (fun j _ => hTotalStep j)
  have hCoefficient : 2 * G * M ^ (n + 1) = K := by
    dsimp only [K, G, M]
    ring
  have hFinal : (∑' p : Cell (n + 2), ENNReal.ofReal (energy (n + 2) p)) ≤
      K * (t * ENNReal.ofReal A₀ + t⁻¹ * ENNReal.ofReal D₀) := by
    simpa only [total, hCoefficient] using hBound
  have hCount : 0 < count := by
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨⟨0, by omega⟩, ?_⟩⟩
    exact ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  have hKPos : 0 < K := by dsimp only [K]; positivity
  have hKFinite : K ≠ ⊤ := by dsimp only [K]; finiteness
  have hMassFinite : t * ENNReal.ofReal A₀ + t⁻¹ * ENNReal.ofReal D₀ ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top htFinite ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ht₀) ENNReal.ofReal_ne_top⟩
  exact ⟨hKPos, hKFinite, hFinal, ne_top_of_le_ne_top (ENNReal.mul_ne_top hKFinite hMassFinite) hFinal⟩

end StratificationTheory
