module

public import StratificationTheory.Foundation.OriginalEnergyFaceTraceGrid
import StratificationTheory.Foundation.OriginalNeighborFaceTrace

/-!
# One native grid retaining the original closed-target line and face data

The original pair supplies its actual energy and discrepancy channels,
original closed-target ACL representatives, raw target values, full face
weak graphs and trace compatibility on the same selected lattice. Each face
prism has one continuous native L2 curve with both original raw endpoint
classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- One offset simultaneously gives the original pair's native all-face weak
graphs, both scalar channels, and one continuous curve with both original raw
endpoint classes for each qualified face prism. Original weak and trace
qualifications are produced from the original ball data before selection. -/
theorem exists_grid_translate_original_closed_target_face_joint
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
    {ε : ℝ} (hε : 0 < ε) :
    let E := (ball z₀ R).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let D := (ball z₀ R).indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let normal := fun i => p i (Fin.natAdd n (0 : Fin 1))
    let v := fun i => EuclideanSpace.single (normal i) (1 : ℝ)
    let β := fun i (y : Domain (n + 1)) => (e ((Q i).symm y)).1
    let B := fun i (t : Domain (k i)) =>
      ∑ s : Fin (k i), t s • EuclideanSpace.single (face i s) (1 : ℝ)
    let W := fun l i => coordinatePermACLRepresentative (p i) (a i) (b i) (w l) (Dw l)
    let line := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let Ω := fun i => {y : Domain (n + 1) |
      β i y ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let L := fun (l : Fin 2) (i : ι) (y : Domain (n + 1)) => y ∈ Ω i →
      W l i y = w l y ∧
      MemLp (fun t => w l (line i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
      MemLp (fun t => Dw l (line i (β i y) t) (normal i))
        2 (volume.restrict (Ioo (a i) (b i))) ∧
      AbsolutelyContinuousOnInterval (fun t => W l i (line i (β i y) t)) (a i) (b i) ∧
      (fun t => W l i (line i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
        (fun t => w l (line i (β i y) t)) ∧
      (∀ t ∈ Icc (a i) (b i), W l i (line i (β i y) t) ∈ N) ∧
      ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
        W l i (line i (β i y) t) - W l i (line i (β i y) s) =
          ∫ r in s..t, Dw l (line i (β i y) r) (normal i)
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
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : ι),
        L l i (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) ∧
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2),
        WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset) ∈ ball z₀ R →
          w l (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) ∈ N) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range grid)),
        ∀ᵐ t ∂volume.restrict (C j),
          (∀ (l : Fin 2) (i : ι), L l i (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ∧
          ∀ l : Fin 2,
            A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t ∈ ball z₀ R →
              w l (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t) ∈ N) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          E (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
                ((∫ x in ball z₀ R, hsNormSq (Dw 0 x)) +
                 (∫ x in ball z₀ R, hsNormSq (Dw 1 x)))) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          D (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal (∫ x in ball z₀ R, ‖w 0 x - w 1 x‖ ^ 2)) ∧
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
  intro E D Q e normal v β B W line Ω L A G grid C
  generalize hLdef : L = L₀
  have hSourceTrace := ae_all_iff.mpr fun l : Fin 2 =>
    ae_original_cubical_face_family_raw_trace hR (hSob l) hN (hTarget l)
      k p face hface S hS a b hab hrect
  have hACL : ∀ᵐ y ∂volume, ∀ (l : Fin 2) (i : ι), L₀ l i y := by
    rw [← hLdef]
    exact ae_all_iff.mpr fun l : Fin 2 =>
      ae_coordinate_acl_closed_target_qualification hR (hSob l) hN.isClosed (hTarget l)
        p S hS a b hab hrect
  have hRawTarget : ∀ᵐ y ∂volume, ∀ l : Fin 2, y ∈ ball z₀ R → w l y ∈ N :=
    ae_all_iff.mpr fun l => (ae_restrict_iff' measurableSet_ball).mp (hTarget l)
  have hSource := hSourceTrace.and (hACL.and hRawTarget)
  generalize hPdef : (fun y : Domain (n + 1) => _) = P at hSource
  obtain ⟨hE, hD, hEfinite, hDfinite, _hEdirichlet, hDreal, hEreal⟩ :=
    original_pair_ball_energy_discrepancy_channels (hSob 0) (hSob 1)
  obtain ⟨offset, hoffset, hvertex, hfiber, henergy, hdiscrepancy⟩ :=
    exists_grid_translate_native_cubical_face_pair_energy hR (hSob 0) (hSob 1)
      d sampleFace hε hE hD hEfinite hDfinite hSource
  rw [← hPdef] at hvertex hfiber
  refine ⟨offset, hoffset, fun z => (hvertex z).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z => (hvertex z).1.2.1
  · exact fun z => (hvertex z).1.2.2
  · intro j z
    exact (hfiber j z).mono fun _ ht => ⟨ht.1.2.1, ht.1.2.2⟩
  · intro j
    simpa only [hEreal] using henergy j
  · intro j
    simpa only [hDreal] using hdiscrepancy j
  ·
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
    obtain ⟨H, hH, hf₀, _hHunique⟩ := (hvertex z).1.1 l i hy₀ U hUfinite hbase
    obtain ⟨K, hK, hg₀, _hKunique⟩ := (hvertex z').1.1 l i hy'qualified U hUfinite hbase'
    obtain ⟨hf₀, hH₀⟩ := hf₀
    obtain ⟨hg₀, hK₀⟩ := hg₀
    change MemLp (fun s => w l (y' + B i s)) 2 (volume.restrict U.val) at hg₀
    obtain ⟨J, hJ, hJ₀, hJε, hJunique⟩ :=
      exists_one_raw_face_trace_between_neighbor_origins hε hy₀ hy'qualified hy'normal
        (w l) (B i) y y' (v i) hy' H K hH hK hf₀ hH₀ hg₀ hK₀
    refine ⟨J, hJ, ⟨hf₀, hJ₀⟩, ?_, hJunique⟩
    refine ⟨?_, ?_⟩
    · simpa only [hy'] using hg₀
    · simpa only [hy'] using hJε

end StratificationTheory
