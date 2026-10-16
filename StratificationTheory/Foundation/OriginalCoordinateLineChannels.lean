module

public import StratificationTheory.Foundation.NativeSelectedFaceEnergy
public import StratificationTheory.Foundation.NativeIntervalL2Trace
public import StratificationTheory.Foundation.IntervalSobolevProductBase

/-! # Original real edge energies and their selected native channels -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Evaluation of the sole native coordinate preserves the lower integral
for arbitrary nonnegative densities, without a measurability premise. -/
theorem lintegral_native_one_cube_eq_real_interval (a b : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x : Domain 1 in ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo a b, f (x 0)) =
      ∫⁻ s in Ioo a b, f s := by
  rw [native_one_cube_eq_interval]
  have hm := measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := a) (b := b))
  exact hm.lintegral_comp_emb
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph.measurableEmbedding f

/-- The nonnegative real integral is bounded by the corresponding lower
integral. This assertion alone does not claim integrability. -/
theorem ofReal_nonnegative_integral_le_lintegral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (hNonneg : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hInt : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hNonneg)).le
  · rw [integral_undef hInt, ENNReal.ofReal_zero]
    exact zero_le

/-- A pointwise raw real-edge density is bounded by the same actual native
half-open edge channel on its original physical parametrization. -/
theorem lintegral_real_edge_le_native_channel {N : ℕ} {ε : ℝ}
    (y : Domain N) (k : Fin N) (f : Domain N → ℝ≥0∞) (g : ℝ → ℝ≥0∞)
    (hPoint : ∀ s ∈ Ioo (0 : ℝ) ε, g s ≤ f (y + s • EuclideanSpace.single k (1 : ℝ))) :
    (∫⁻ s in Ioo (0 : ℝ) ε, g s) ≤
      ∫⁻ x : Domain 1 in ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε,
        f (y + x 0 • EuclideanSpace.single k (1 : ℝ)) := by
  calc
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) ε, f (y + s • EuclideanSpace.single k (1 : ℝ)) :=
      setLIntegral_mono' measurableSet_Ioo hPoint
    _ = ∫⁻ x : Domain 1 in ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
        f (y + x 0 • EuclideanSpace.single k (1 : ℝ)) :=
      (lintegral_native_one_cube_eq_real_interval 0 ε _).symm
    _ ≤ _ := lintegral_mono_set (by
      intro x hx
      exact mem_iInter.mpr fun j => ⟨(mem_iInter.mp hx j).1.le, (mem_iInter.mp hx j).2⟩)

private theorem original_column_sq_le_hs {N q : ℕ} (D : Gradient N q) (k : Fin N) :
    ‖D k‖ ^ 2 ≤ hsNormSq D := by
  have h := hsNormSq_coordinate_embedding_le
    (⟨fun _ : Fin 1 => k, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin N) D
  simpa only [hsNormSq, Fin.sum_univ_one, Function.Embedding.coeFn_mk] using h

/-- Both original real gradient-column integrals are bounded jointly by
one native ambient HS channel on the very same physical edge. -/
theorem original_real_edge_separate_energies_le_native_channel {N q : ℕ} {ε R : ℝ}
    (y : Domain N) (k : Fin N) (Dw : Fin 2 → Domain N → Gradient N q)
    (hImage : ∀ s ∈ Ioo (0 : ℝ) ε,
      y + s • EuclideanSpace.single k (1 : ℝ) ∈ ball (0 : Domain N) R) :
    let Eraw := (ball (0 : Domain N) R).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    ENNReal.ofReal ((∫ s in Ioo (0 : ℝ) ε, ‖Dw 0 (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2) +
      ∫ s in Ioo (0 : ℝ) ε, ‖Dw 1 (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2) ≤
      ∫⁻ x : Domain 1 in ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε,
        Eraw (y + x 0 • EuclideanSpace.single k (1 : ℝ)) := by
  intro Eraw
  let f := fun (l : Fin 2) (s : ℝ) => ‖Dw l (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2
  have hNonneg (l : Fin 2) : 0 ≤ ∫ s in Ioo (0 : ℝ) ε, f l s :=
    integral_nonneg fun s => sq_nonneg _
  rw [ENNReal.ofReal_add (hNonneg 0) (hNonneg 1)]
  calc
    _ ≤ (∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal (f 0 s)) +
        ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal (f 1 s) :=
      add_le_add (ofReal_nonnegative_integral_le_lintegral _ (fun _ => sq_nonneg _))
        (ofReal_nonnegative_integral_le_lintegral _ (fun _ => sq_nonneg _))
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal (f 0 s) + ENNReal.ofReal (f 1 s) := le_lintegral_add _ _
    _ ≤ _ := lintegral_real_edge_le_native_channel y k Eraw _ (by
      intro s hs
      dsimp only [Eraw, f]
      rw [Set.indicator_of_mem (hImage s hs), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact add_le_add (original_column_sq_le_hs _ k) (original_column_sq_le_hs _ k))

/-- The original combined real edge energy used in the square-root tube
term is controlled by the same native HS channel. -/
theorem original_real_edge_combined_energy_le_native_channel {N q : ℕ} {ε R : ℝ}
    (y : Domain N) (k : Fin N) (Dw : Fin 2 → Domain N → Gradient N q)
    (hImage : ∀ s ∈ Ioo (0 : ℝ) ε,
      y + s • EuclideanSpace.single k (1 : ℝ) ∈ ball (0 : Domain N) R) :
    let Eraw := (ball (0 : Domain N) R).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    ENNReal.ofReal (∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2 +
        ‖Dw 1 (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2) ≤
      ∫⁻ x : Domain 1 in ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε,
        Eraw (y + x 0 • EuclideanSpace.single k (1 : ℝ)) := by
  intro Eraw
  calc
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal
        (‖Dw 0 (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2 +
          ‖Dw 1 (y + s • EuclideanSpace.single k (1 : ℝ)) k‖ ^ 2) :=
      ofReal_nonnegative_integral_le_lintegral _ (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ _ := lintegral_real_edge_le_native_channel y k Eraw _ (by
      intro s hs
      dsimp only [Eraw]
      rw [Set.indicator_of_mem (hImage s hs)]
      exact ENNReal.ofReal_le_ofReal (add_le_add (original_column_sq_le_hs _ k) (original_column_sq_le_hs _ k)))

/-- The original real edge discrepancy uses the same physical map and the
same native discrepancy channel; no trace or connector premise is needed. -/
theorem original_real_edge_discrepancy_le_native_channel {N q : ℕ} {ε R : ℝ}
    (y : Domain N) (k : Fin N) (w : Fin 2 → Domain N → Ambient q)
    (hImage : ∀ s ∈ Ioo (0 : ℝ) ε,
      y + s • EuclideanSpace.single k (1 : ℝ) ∈ ball (0 : Domain N) R) :
    let Draw := (ball (0 : Domain N) R).indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    ENNReal.ofReal (∫ s in Ioo (0 : ℝ) ε,
      ‖w 0 (y + s • EuclideanSpace.single k (1 : ℝ)) - w 1 (y + s • EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤
      ∫⁻ x : Domain 1 in ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε,
        Draw (y + x 0 • EuclideanSpace.single k (1 : ℝ)) := by
  intro Draw
  calc
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal
        (‖w 0 (y + s • EuclideanSpace.single k (1 : ℝ)) - w 1 (y + s • EuclideanSpace.single k (1 : ℝ))‖ ^ 2) :=
      ofReal_nonnegative_integral_le_lintegral _ (fun _ => sq_nonneg _)
    _ ≤ _ := lintegral_real_edge_le_native_channel y k Draw _ (by
      intro s hs
      dsimp only [Draw]
      rw [Set.indicator_of_mem (hImage s hs)])

end StratificationTheory
