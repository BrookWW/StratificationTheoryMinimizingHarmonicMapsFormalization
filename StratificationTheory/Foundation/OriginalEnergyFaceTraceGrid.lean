module

public import StratificationTheory.Foundation.OriginalFaceTraceGridSampling
public import StratificationTheory.Foundation.OriginalGridEnergyChannels

/-!
# The original pair's energy and discrepancy on one trace-compatible grid

The scalar channels are the original ball indicators of Hilbert--Schmidt
energy and squared discrepancy. One offset supplies their native bounds,
all original face weak graphs, and one continuous L2 curve with both raw
endpoint classes on every qualified original face prism.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- One offset simultaneously gives the original pair's native all-face weak
graphs, both scalar channels, and one continuous curve with both original raw
endpoint classes for each qualified face prism. Original weak and trace
qualifications are produced from the original ball data before selection. -/
theorem exists_grid_translate_original_energy_face_trace_pair
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
  intro E D Q e normal v β B A G grid C
  obtain ⟨hE, hD, hEfinite, hDfinite, _hEdirichlet, hDreal, hEreal⟩ :=
    original_pair_ball_energy_discrepancy_channels (hSob 0) (hSob 1)
  obtain ⟨offset, hoffset, hweak, henergy, hdiscrepancy, htrace⟩ :=
    exists_grid_translate_original_face_trace_pair_energy hR w Dw hSob hN hTarget
      k p face hface S hS a b hab hrect d sampleFace hε hE hD hEfinite hDfinite
  refine ⟨offset, hoffset, hweak, ?_, ?_, htrace⟩
  · intro j
    simpa only [hEreal] using henergy j
  · intro j
    simpa only [hDreal] using hdiscrepancy j

end StratificationTheory
