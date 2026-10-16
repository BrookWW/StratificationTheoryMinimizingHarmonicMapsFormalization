module

public import StratificationTheory.Foundation.OriginalCubicalFaceTrace
public import StratificationTheory.Foundation.NativeCubicalFaceGridSampling
public import StratificationTheory.Foundation.GridNeighborCoordinates
public import StratificationTheory.Foundation.TranslatedL2TraceCompatibility

/-!
# One original grid with full face weak graphs and double-endpoint traces

One selected lattice retains the original weak graphs and both scalar
channels. The two endpoint classes of each original face prism belong to one
continuous native L2 curve. The upper class is derived from the same lattice's
neighboring vertex and whole-curve translation uniqueness.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- One offset simultaneously gives the original pair's native all-face weak
graphs, both scalar channels, and one continuous curve with both original raw
endpoint classes for each qualified face prism. Original weak and trace
qualifications are produced from the original ball data before selection. -/
theorem exists_grid_translate_original_face_trace_pair_energy
    {n q : ℕ} {ι J : Type*} [Countable ι] [Fintype J]
    {z₀ : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    (w : Fin 2 → Domain (n + 1) → Ambient q)
    (Dw : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (hSob : ∀ l, MemW12 (ballDomain z₀ R) (w l) (Dw l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ y ∂volume.restrict (ball z₀ R), w l y ∈ N)
    (k : ι → ℕ) (p : ι → Equiv.Perm (Fin (n + 1)))
    (face : ∀ i, Fin (k i) ↪ Fin (n + 1))
    (hface : ∀ i l, face i l ≠ p i (Fin.natAdd n (0 : Fin 1)))
    (S : ι → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z₀ R)
    (d : J → ℕ) (sampleFace : ∀ j, Fin (d j) ↪ Fin (n + 1))
    {ε : ℝ} (hε : 0 < ε)
    {f g : Domain (n + 1) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hfFinite : (∫⁻ x, f x) ≠ ⊤)
    (hgFinite : (∫⁻ x, g x) ≠ ⊤) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let normal := fun i => p i (Fin.natAdd n (0 : Fin 1))
    let v := fun i => EuclideanSpace.single (normal i) (1 : ℝ)
    let β := fun i (y : Domain (n + 1)) => (e ((Q i).symm y)).1
    let B := fun i (t : Domain (k i)) =>
      ∑ s : Fin (k i), t s • EuclideanSpace.single (face i s) (1 : ℝ)
    let A := fun j (y : Domain (n + 1)) (t : Domain (d j)) =>
      y + ∑ s : Fin (d j), t s • EuclideanSpace.single (sampleFace j s) (1 : ℝ)
    let G : Domain (n + 1) → Prop := fun y => ∀ (j : J) (U : OpenDomain (d j)),
      (∀ t ∈ U.val, A j y t ∈ ball z₀ R) →
      MemW12 U (fun t => w 0 (A j y t)) (fun t s => Dw 0 (A j y t) (sampleFace j s)) ∧
      MemW12 U (fun t => w 1 (A j y t)) (fun t s => Dw 1 (A j y t) (sampleFace j s))
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _j : Fin (n + 1) => ε) (fun _j => hε.ne'.isUnit)
    let C := fun j => ⋂ s : Fin (d j), (EuclideanSpace.proj s) ⁻¹' Ico (0 : ℝ) ε
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ s, offset s ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range grid),
        G (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          f (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ∫⁻ x, f x) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          g (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ∫⁻ x, g x) ∧
      ∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : ι),
        let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
        y (normal i) ∈ Ioo (a i) (b i) →
        y (normal i) + ε ∈ Ioo (a i) (b i) →
        ∀ U : OpenDomain (k i), (volume : Measure (Domain (k i))) U.val ≠ ⊤ →
        (∀ s ∈ U.val, β i (y + B i s) ∈ S i) →
        ∃ H : C(Icc (0 : ℝ) ε,
            Lp (Ambient q) 2 ((volume : Measure (Domain (k i))).restrict U.val)),
          (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
            ∃ hslice : MemLp (fun s => w l (y + B i s + r • v i)) 2 (volume.restrict U.val),
              H ⟨r, hr.1.le, hr.2.le⟩ =
                hslice.toLp (fun s => w l (y + B i s + r • v i))) ∧
          (∃ hleft : MemLp (fun s => w l (y + B i s)) 2 (volume.restrict U.val),
            H ⟨0, le_rfl, hε.le⟩ = hleft.toLp (fun s => w l (y + B i s))) ∧
          (∃ hright : MemLp (fun s => w l (y + ε • v i + B i s)) 2 (volume.restrict U.val),
            H ⟨ε, hε.le, le_rfl⟩ = hright.toLp (fun s => w l (y + ε • v i + B i s))) ∧
          ∀ K : C(Icc (0 : ℝ) ε,
              Lp (Ambient q) 2 ((volume : Measure (Domain (k i))).restrict U.val)),
            (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
              ∃ hslice : MemLp (fun s => w l (y + B i s + r • v i)) 2 (volume.restrict U.val),
                K ⟨r, hr.1.le, hr.2.le⟩ =
                  hslice.toLp (fun s => w l (y + B i s + r • v i))) → K = H := by
  intro Q e normal v β B A G grid C
  have hSource := ae_all_iff.mpr fun l : Fin 2 =>
    ae_original_cubical_face_family_raw_trace hR (hSob l) hN (hTarget l)
      k p face hface S hS a b hab hrect
  obtain ⟨offset, hoffset, hvertex, _hfiber, henergy, hdiscrepancy⟩ :=
    exists_grid_translate_native_cubical_face_pair_energy hR (hSob 0) (hSob 1)
      d sampleFace hε hf hg hfFinite hgFinite hSource
  refine ⟨offset, hoffset, fun z => (hvertex z).2, henergy, hdiscrepancy, ?_⟩
  intro z l i y hy₀ hyε U hUfinite hbase
  obtain ⟨z', hz'⟩ := exists_scaled_grid_neighbor hε offset z (normal i)
  let y' := WithLp.toLp 2 ((z' : Fin (n + 1) → ℝ) + offset)
  have hy' : y' = y + ε • v i := hz'
  have hy'normal : y' (normal i) = y (normal i) + ε := by
    rw [hy']
    change y (normal i) + ε * (Pi.single (normal i) (1 : ℝ) : Fin (n + 1) → ℝ) (normal i) = _
    rw [Pi.single_eq_same, mul_one]
  have hy'qualified : y' (normal i) ∈ Ioo (a i) (b i) := by
    rwa [hy'normal]
  have hbase' : ∀ s ∈ U.val, β i (y' + B i s) ∈ S i := by
    intro s hs
    have hcoords := coordinate_normal_translation_coordinates (p i) (y + B i s) ε
    have heq : y' + B i s = y + B i s + ε • v i := by rw [hy']; abel
    rw [heq]
    have hβ : β i (y + B i s + ε • v i) = β i (y + B i s) := hcoords.1
    rw [hβ]
    exact hbase s hs
  obtain ⟨H, hH, hf₀, _hHunique⟩ := (hvertex z).1 l i hy₀ U hUfinite hbase
  obtain ⟨K, hK, hg₀, _hKunique⟩ := (hvertex z').1 l i hy'qualified U hUfinite hbase'
  obtain ⟨hf₀, hH₀⟩ := hf₀
  obtain ⟨hg₀, hK₀⟩ := hg₀
  change MemLp (fun s => w l (y' + B i s)) 2 (volume.restrict U.val) at hg₀
  let F : Domain (k i) × ℝ → Ambient q := fun sr => w l (y + B i sr.1 + sr.2 • v i)
  let F' : Domain (k i) × ℝ → Ambient q := fun sr => w l (y' + B i sr.1 + sr.2 • v i)
  have hclosed : ∀ r ∈ Icc (a i - y (normal i)) (b i - y (normal i)),
      r - ε ∈ Icc (a i - y' (normal i)) (b i - y' (normal i)) := by
    intro r hr
    rw [hy'normal]
    exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hopen : ∀ r ∈ Ioo (a i - y (normal i)) (b i - y (normal i)),
      r - ε ∈ Ioo (a i - y' (normal i)) (b i - y' (normal i)) := by
    intro r hr
    rw [hy'normal]
    exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hraw (s : Domain (k i)) (r : ℝ) : F' (s, r - ε) = F (s, r) := by
    dsimp only [F', F]
    rw [hy', sub_smul]
    congr 1
    abel
  have hha : a i - y (normal i) < 0 := sub_neg.mpr hy₀.1
  have hhb : ε < b i - y (normal i) := by linarith only [hyε.2]
  have hhc : a i - y' (normal i) < 0 := sub_neg.mpr hy'qualified.1
  have hhd : 0 < b i - y' (normal i) := sub_pos.mpr hy'qualified.2
  have hF₀ : MemLp (fun s => F (s, 0)) 2 (volume.restrict U.val) := by
    simpa only [F, zero_smul, add_zero] using hf₀
  have hF'₀ : MemLp (fun s => F' (s, 0)) 2 (volume.restrict U.val) := by
    simpa only [F', zero_smul, add_zero] using hg₀
  have hH₀' : H ⟨0, hha.le, (hε.trans hhb).le⟩ = hF₀.toLp (fun s => F (s, 0)) := by
    simpa only [F, zero_smul, add_zero] using hH₀
  have hK₀' : K ⟨0, hhc.le, hhd.le⟩ = hF'₀.toLp (fun s => F' (s, 0)) := by
    simpa only [F', zero_smul, add_zero] using hK₀
  obtain ⟨J, _hJrestrict, hJ, hJ₀, hJε, hJunique⟩ :=
    exists_one_L2_trace_between_translated_raw_cuts hε hha hhb hhc hhd H K hH hK
      hclosed hopen hraw hF₀ hH₀' hF'₀ hK₀'
  refine ⟨J, hJ, ?_, ?_, hJunique⟩
  · exact ⟨hf₀, by simpa only [F, zero_smul, add_zero] using hJ₀⟩
  · refine ⟨?_, ?_⟩
    · simpa only [hy'] using hg₀
    · simpa only [F', zero_smul, add_zero, hy'] using hJε

end StratificationTheory
