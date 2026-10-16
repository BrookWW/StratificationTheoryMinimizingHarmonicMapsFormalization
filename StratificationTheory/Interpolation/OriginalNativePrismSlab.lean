module

public import StratificationTheory.Interpolation.OriginalUniformPrismEstimates
public import StratificationTheory.Foundation.CanonicalPrismUnitMeshAssembly
public import StratificationTheory.Foundation.SelectedGridFiniteActiveCells

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology BigOperators ENNReal
namespace StratificationTheory

/-- One original Sobolev pair produces an actual full-dimensional weak
map on an interior spatial cube times the original time interval.
The physical mesh has the coupled energy bound and the frozen ambient
powers for its distance from the target. -/
theorem exists_original_ball_native_prism_slab {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    (N : Set (Ambient q)) (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < (1 / 8 : ℝ)) :
    let J := (r : Fin (n + 3)) × (Fin r.val ↪ Fin (n + 2))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let K : ℝ≥0∞ := 4 * (Fintype.card J : ℝ≥0∞) * (Fintype.card J : ℝ≥0∞) *
      (6 * ((n + 3 : ℕ) : ℝ≥0∞)) ^ (n + 1)
    let BTube := ((2 : ℝ) ^ (n + 1) * ((n + 2).factorial : ℝ)) *
      ((4 * (Fintype.card J : ℝ)) * ε ^ ((1 : ℤ) - ((n + 2 : ℕ) : ℤ)) * Real.sqrt A₀ * Real.sqrt D₀ +
        (4 * (Fintype.card J : ℝ)) * ε ^ (-((n + 2 : ℕ) : ℤ)) * D₀)
    ∃ base : Domain (n + 2),
      let U : OpenDomain (n + 2) :=
        ⟨⋂ j : Fin (n + 2), (fun x : Domain (n + 2) => base j + x j) ⁻¹' Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ),
          isOpen_iInter_of_finite (fun j : Fin (n + 2) =>
            isOpen_Ioo.preimage (continuous_const.add (EuclideanSpace.proj j).continuous))⟩
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 2) (m := 1)
      let Ω : OpenDomain (n + 3) :=
        ⟨{x | (e x).1 ∈ U.val ∧ (e x).2 0 ∈ Ioo (0 : ℝ) ε},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ (W : Domain (n + 3) → Ambient q) (D : Domain (n + 3) → Gradient (n + 3) q) (M : ℝ),
        MemW12 Ω W D ∧ (0 ≤ M ∧ ∀ z ∈ N, ‖z‖ ≤ M) ∧
        (∀ᵐ x ∂volume.restrict Ω.val, ‖W x‖ ≤ M) ∧
        ENNReal.ofReal (∫ x in Ω.val, hsNormSq (D x)) ≤
          K * (ENNReal.ofReal ε * ENNReal.ofReal A₀ +
            (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal D₀) ∧
        ∀ᵐ x ∂volume.restrict Ω.val, (infDist (W x) N) ^ 2 ≤ BTube := by
  classical
  intro J A₀ D₀ K BTube
  obtain ⟨offset, hOffset, _hSelectE, _hSelectD, hFamily⟩ :=
    exists_original_ball_uniform_prism_family_with_estimates w Dw hSob N hN hTarget ε hε
  dsimp (config := {zeta := false}) only at hFamily
  let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
    (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
  let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
    StrictMono (c.val.1 : Fin r → Fin (n + 2))}
  let B := fun r : ℕ => (⟨⋂ j : Fin r, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
    isOpen_iInter_of_finite (fun j : Fin r => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩ : OpenDomain r)
  obtain ⟨V, DV, H, child, frame, Tube, _HS, M, hCore, hEnergy, hTube⟩ := hFamily
  have hM := hCore.1
  have hW := hCore.2.2.2.2.2.2.1
  have hNorm := hCore.2.2.2.2.2.2.2.1
  have hRaw := hCore.2.2.2.2.2.2.2.2.1
  have hTime := hCore.2.2.2.2.2.2.2.2.2.1
  have hFields := hCore.2.2.2.2.2.2.2.2.2.2.1
  have hDist := hCore.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hCore _hSelectE _hSelectD
  obtain ⟨k, _hk, node, hNodeCoord, hNodeInj, hNodeOrigin, hHost⟩ :=
    selected_grid_finite_mesh_frame hε offset hOffset
  let L := 2 * k + 1
  let base : Domain (n + 2) := WithLp.toLp 2 (fun j => offset j - (k : ℝ) * ε)
  let sourceOrigin := fun α : Fin (n + 2) → Fin L =>
    WithLp.toLp 2 ((node α : Fin (n + 2) → ℝ) + offset)
  let Valid := {α : Fin (n + 2) → Fin L // ∀ t : Domain (n + 2),
    (∀ j, t j ∈ Icc (0 : ℝ) ε) → ∀ j, (sourceOrigin α + t) j ∈ Ioo (-1 : ℝ) 1}
  obtain ⟨idx, hIdxAxes, hIdxOrigin, _hIdxSum⟩ :=
    selected_grid_finite_actual_cell_embedding grid offset ε node hNodeInj
  refine ⟨base, ?_⟩
  intro U e Ω
  let spatial := fun z : Fin (n + 3) → Fin L => fun j : Fin (n + 2) => z j.castSucc
  let active := fun z : Fin (n + 3) → Fin L => (z (Fin.last (n + 2))).val = 0 ∧
    ∀ t : Domain (n + 2), (∀ j, t j ∈ Icc (0 : ℝ) ε) →
      ∀ j, (sourceOrigin (spatial z) + t) j ∈ Ioo (-1 : ℝ) 1
  let index : (z : Fin (n + 3) → Fin L) → active z → Cell (n + 2) :=
    fun z hz => idx ⟨spatial z, hz.2⟩
  have hActive z (hz : ∃ x ∈ Ω.val, ∀ i,
      x i ∈ Icc ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε)) : active z := by
    obtain ⟨x, hx, hxCell⟩ := hz
    have ht : x (Fin.last (n + 2)) ∈ Ioo (0 : ℝ) ε := hx.2
    refine ⟨?_, ?_⟩
    · by_contra hnot
      have hpos : (1 : ℝ) ≤ (z (Fin.last (n + 2))).val := by exact_mod_cast Nat.pos_of_ne_zero hnot
      have hh := (hxCell (Fin.last (n + 2))).1
      nlinarith [ht.2]
    · apply selected_grid_active_closed_cell_contained hε hεsmall
      refine ⟨base + (e x).1, ?_, ?_⟩
      · intro j
        exact abs_lt.mpr (mem_iInter.mp hx.1 j)
      · intro j
        rw [show sourceOrigin (spatial z) = base + WithLp.toLp 2 (fun j => ((z j.castSucc).val : ℝ) * ε) from hNodeOrigin (spatial z)]
        have hj := hxCell j.castSucc
        change base j + x j.castSucc ∈ Icc (base j + ((z j.castSucc).val : ℝ) * ε)
          (base j + ((z j.castSucc).val : ℝ) * ε + ε)
        constructor <;> nlinarith [hj.1, hj.2]
  have hΩsub : Ω.val ⊆ (uniformGridBox (n + 3) L ε).val := by
    intro x hx
    have hh := hHost (base + (e x).1) (fun j => abs_lt.mpr (mem_iInter.mp hx.1 j))
    rw [mem_uniformGridBox_iff] at hh ⊢
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have ht : x (Fin.last (n + 2)) ∈ Ioo (0 : ℝ) ε := hx.2
      have hL : (1 : ℝ) ≤ L := by dsimp only [L]; exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (by nlinarith)⟩
    · have hj := hh j
      change 0 < (base j + x j.castSucc) - base j ∧ (base j + x j.castSucc) - base j < (L : ℝ) * ε at hj
      exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
  have hIndexAxes z hz : (index z hz).val.val.1 = Function.Embedding.refl _ := hIdxAxes _
  have hIndexOrigin z hz : (index z hz).val.val.2 = base +
      WithLp.toLp 2 (fun j : Fin (n + 2) => ((z j.castSucc).val : ℝ) * ε) :=
    (hIdxOrigin _).trans (hNodeOrigin (spatial z))
  let cap := fun (c : Cell (n + 2)) (side : Bool) =>
    w (if side then 1 else 0) ∘ (fun x : Domain (n + 2) => c.val.val.2 +
      ∑ j, ((WithLp.toLp 2 (fun _ : Fin (n + 2) => ε / 2) + (ε / 2) • x) j) •
        EuclideanSpace.single (c.val.val.1 j) (1 : ℝ))
  obtain ⟨W, D, hFull, hSlabE, hPoint, hProp⟩ :=
    memW12_uniform_grid_from_canonical_prism_family grid offset hε V DV child frame cap
      (fun r c i side => (hFields r c i side).1)
      (fun r c i side => (hFields r c i side).2.1)
      (fun r c i side => (hFields r c i side).2.2.1)
      (fun r c i side => (hFields r c i side).2.2.2.1)
      (fun c => hW (n + 2) c) M hM.1 (fun c => hNorm (n + 2) c)
      (H (n + 2)) (hRaw (n + 2)) (hTime (n + 2))
      (fun c i side => (hFields (n + 1) c i side).2.2.2.2.2)
      Ω hΩsub (fun x hx => hx.2) active hActive index base hIndexAxes hIndexOrigin
  refine ⟨W, D, M, hFull, hM, hProp (fun z => ‖z‖ ≤ M) (fun z hz _ => hNorm (n + 2) (index z hz)), ?_, ?_⟩
  · let unitE : (Fin (n + 3) → Fin L) → ℝ := fun z =>
      if hz : active z then ∫ x in (B (n + 3)).val, hsNormSq (DV (n + 2) (index z hz) x) else 0
    let F : Cell (n + 2) → ℝ≥0∞ := fun c => ENNReal.ofReal
      ((ε / 2) ^ (((n + 2 : ℕ) : ℤ) - 1) * ∫ x in (B (n + 3)).val, hsNormSq (DV (n + 2) c x))
    let meshE : (Fin (n + 3) → Fin L) → ℝ≥0∞ := fun z =>
      if hz : active z then F (index z hz) else 0
    have hIndexInj : Function.Injective (fun z : {z | active z} => index z.val z.property) := by
      intro z z' heq
      have hValid := idx.injective heq
      have hSpatial : spatial z.val = spatial z'.val := congrArg Subtype.val hValid
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · apply Fin.ext
        exact z.property.1.trans z'.property.1.symm
      · exact congrFun hSpatial j
    have hMeshSum : (∑' z : Fin (n + 3) → Fin L, meshE z) ≤ ∑' c : Cell (n + 2), F c :=
      tsum_zero_extension_le_actual_family {z | active z} ⟨_, hIndexInj⟩ F meshE
        (fun z hz => by change ¬ active z at hz; simp only [meshE, dif_neg hz])
        (fun z => by have hz : active z.val := z.property; simp only [meshE, dif_pos hz]; exact le_rfl)
    have hPower : (((n + 2 : ℕ) : ℤ) - 1) = (n + 1 : ℕ) := by omega
    have hNonneg z : 0 ≤ (ε / 2) ^ (n + 1) * unitE z := by
      apply mul_nonneg (pow_nonneg (div_pos hε (by norm_num)).le _)
      dsimp only [unitE]
      split_ifs
      · exact integral_nonneg fun _ => hsNormSq_nonneg _
      · exact le_rfl
    have hFiniteSum : ENNReal.ofReal ((ε / 2) ^ (n + 1) * ∑ z, unitE z) = ∑' z, meshE z := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun z _ => hNonneg z), tsum_fintype]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : active z
      · simp only [unitE, meshE, dif_pos hz, F, hPower, zpow_natCast]
      · simp only [unitE, meshE, dif_neg hz, mul_zero, ENNReal.ofReal_zero]
    have hSlabE' : (∫ x in Ω.val, hsNormSq (D x)) ≤ (ε / 2) ^ (n + 1) * ∑ z, unitE z := by
      with_reducible simpa only [unitE, B] using hSlabE
    calc
      ENNReal.ofReal (∫ x in Ω.val, hsNormSq (D x)) ≤
          ENNReal.ofReal ((ε / 2) ^ (n + 1) * ∑ z, unitE z) := ENNReal.ofReal_le_ofReal hSlabE'
      _ = ∑' z, meshE z := hFiniteSum
      _ ≤ ∑' c : Cell (n + 2), F c := hMeshSum
      _ ≤ _ := hEnergy.2.2.1
  · apply hProp (fun z => (infDist z N) ^ 2 ≤ BTube)
    intro z hz _
    exact (hDist (n + 2) (index z hz)).mono fun x hx => hx.trans (hTube (n + 1) (index z hz))

end StratificationTheory
