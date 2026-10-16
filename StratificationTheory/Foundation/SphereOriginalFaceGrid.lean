module

public import StratificationTheory.Foundation.OriginalClosedTargetFaceGridJoint
public import StratificationTheory.Foundation.JointRadialPairData
public import StratificationTheory.Foundation.GridCubeBallContainment
import StratificationTheory.Foundation.CoordinateACLIntegralIncrements

/-!
# One original sphere pair and its complete native grid qualifications

The original named sphere gradients and discrepancy control the two native
mixed-face channels of the same radial pair and the same selected grid. The
source ball radius is fixed by dimension, all unit-cube line inclusions are
proved internally, and the original target values are retained without a
cutoff. Original weak graphs, ACL data and one-curve double-endpoint traces
belong to that same grid.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- One offset simultaneously gives the original pair's native all-face weak
graphs, both scalar channels, and one continuous curve with both original raw
endpoint classes for each qualified face prism. Original weak and trace
qualifications are produced from the original ball data before selection. -/
theorem exists_sphere_pair_original_closed_target_face_grid
    {n q : ℕ} {ι J : Type*} [Countable ι] [Fintype J]
    (hn : 2 ≤ n)
    (u : Fin 2 → sphere (0 : Domain (n + 1)) 1 → Ambient q)
    (hu : ∀ l, MemSphereW12 (by omega : 2 ≤ n + 1) (u l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hSphereTarget : ∀ l, ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure n :
      Measure (sphere (0 : Domain (n + 1)) 1)), u l θ ∈ N)
    (k : ι → ℕ) (p : ι → Equiv.Perm (Fin (n + 1)))
    (face : ∀ i, Fin (k i) ↪ Fin (n + 1))
    (hface : ∀ i l, face i l ≠ p i (Fin.natAdd n (0 : Fin 1)))
    (d : J → ℕ) (sampleFace : ∀ j, Fin (d j) ↪ Fin (n + 1))
    {ε : ℝ} (hε : 0 < ε) :
    let R : ℝ := (n : ℝ) + 2
    let S : Set (Domain n) :=
      ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let A_S : ℝ :=
      (∫ θ : sphere (0 : Domain (n + 1)) 1,
        hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ n + 1) (u 0) (hu 0) i) θ)
          ∂Measure.euclideanHausdorffMeasure n) +
      (∫ θ : sphere (0 : Domain (n + 1)) 1,
        hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ n + 1) (u 1) (hu 1) i) θ)
          ∂Measure.euclideanHausdorffMeasure n)
    let D_S : ℝ := ∫ θ : sphere (0 : Domain (n + 1)) 1, ‖u 0 θ - u 1 θ‖ ^ 2
      ∂Measure.euclideanHausdorffMeasure n
    ∃ (w : Fin 2 → Domain (n + 1) → Ambient q)
      (Dw : Fin 2 → Domain (n + 1) → Gradient (n + 1) q),
      (∀ l, MemW12 (ballDomain 0 R) (w l) (Dw l)) ∧
      (∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 1)) R), w l x ∈ N) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (θ : sphere (0 : Domain (n + 1)) 1),
        w l (ρ.val • θ.val) = u l θ) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (i : Fin (n + 1)),
        (fun θ : sphere (0 : Domain (n + 1)) 1 => ρ.val • Dw l (ρ.val • θ.val) i) =ᵐ[
          Measure.euclideanHausdorffMeasure n]
            (fun θ => (sphereGradient (by omega : 2 ≤ n + 1) (u l) (hu l) i) θ)) ∧
      ((∫ x in ball (0 : Domain (n + 1)) R, hsNormSq (Dw 0 x)) +
        (∫ x in ball (0 : Domain (n + 1)) R, hsNormSq (Dw 1 x))) =
          (R ^ ((n + 1) - 2) / ((n + 1) - 2)) * A_S ∧
      (∫ x in ball (0 : Domain (n + 1)) R, ‖w 0 x - w 1 x‖ ^ 2) =
        (R ^ (n + 1) / (n + 1)) * D_S ∧
    let E := (ball (0 : Domain (n + 1)) R).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let D := (ball (0 : Domain (n + 1)) R).indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let normal := fun i => p i (Fin.natAdd n (0 : Fin 1))
    let v := fun i => EuclideanSpace.single (normal i) (1 : ℝ)
    let β := fun i (y : Domain (n + 1)) => (e ((Q i).symm y)).1
    let B := fun i (t : Domain (k i)) =>
      ∑ s : Fin (k i), t s • EuclideanSpace.single (face i s) (1 : ℝ)
    let W := fun l i => coordinatePermACLRepresentative (p i) (-1 : ℝ) (1 : ℝ) (w l) (Dw l)
    let line := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let Ω := fun i => {y : Domain (n + 1) |
      β i y ∈ S ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (-1 : ℝ) (1 : ℝ)}
    let L := fun (l : Fin 2) (i : ι) (y : Domain (n + 1)) => y ∈ Ω i →
      W l i y = w l y ∧
      MemLp (fun t => w l (line i (β i y) t)) 2 (volume.restrict (Ioo (-1 : ℝ) (1 : ℝ))) ∧
      MemLp (fun t => Dw l (line i (β i y) t) (normal i))
        2 (volume.restrict (Ioo (-1 : ℝ) (1 : ℝ))) ∧
      AbsolutelyContinuousOnInterval (fun t => W l i (line i (β i y) t)) (-1 : ℝ) (1 : ℝ) ∧
      (fun t => W l i (line i (β i y) t)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) (1 : ℝ))]
        (fun t => w l (line i (β i y) t)) ∧
      (∀ t ∈ Icc (-1 : ℝ) (1 : ℝ), W l i (line i (β i y) t) ∈ N) ∧
      ∀ s ∈ Icc (-1 : ℝ) (1 : ℝ), ∀ t ∈ Icc (-1 : ℝ) (1 : ℝ),
        W l i (line i (β i y) t) - W l i (line i (β i y) s) =
          ∫ r in s..t, Dw l (line i (β i y) r) (normal i)
    let A := fun j (y : Domain (n + 1)) (t : Domain (d j)) =>
      y + ∑ s : Fin (d j), t s • EuclideanSpace.single (sampleFace j s) (1 : ℝ)
    let G : Domain (n + 1) → Prop := fun y => ∀ (j : J) (U : OpenDomain (d j)),
      (∀ t ∈ U.val, A j y t ∈ ball (0 : Domain (n + 1)) R) →
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
        WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset) ∈ ball (0 : Domain (n + 1)) R →
          w l (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) ∈ N) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range grid)),
        ∀ᵐ t ∂volume.restrict (C j),
          (∀ (l : Fin 2) (i : ι), L l i (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ∧
          ∀ l : Fin 2,
            A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t ∈ ball (0 : Domain (n + 1)) R →
              w l (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t) ∈ N) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          E (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
                ((R ^ ((n + 1) - 2) / ((n + 1) - 2)) * A_S)) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          D (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal ((R ^ (n + 1) / (n + 1)) * D_S)) ∧
      ∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : ι),
        let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
        y (normal i) ∈ Ioo (-1 : ℝ) (1 : ℝ) →
        y (normal i) + ε ∈ Ioo (-1 : ℝ) (1 : ℝ) →
        ∀ U : OpenDomain (k i), (volume : Measure (Domain (k i))) U.val ≠ ⊤ →
        (∀ s ∈ U.val, β i (y + B i s) ∈ S) →
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
  intro R S A_S D_S
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨w, Dw, hW, hraw, hgradient, henergyReal, hdiscrepancyReal, hvalues⟩ :=
    exists_joint_radial_pair_ball_data (by omega : 3 ≤ n + 1) u hu hR
  have hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 1)) R), w l x ∈ N :=
    fun l => hvalues l (fun x => x ∈ N) (hSphereTarget l)
  have henergyReal' :
      ((∫ x in ball (0 : Domain (n + 1)) R, hsNormSq (Dw 0 x)) +
        (∫ x in ball (0 : Domain (n + 1)) R, hsNormSq (Dw 1 x))) =
          (R ^ ((n + 1) - 2) / ((n : ℝ) + 1 - 2)) * A_S := by
    simpa only [A_S, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using henergyReal
  have hdiscrepancyReal' :
      (∫ x in ball (0 : Domain (n + 1)) R, ‖w 0 x - w 1 x‖ ^ 2) =
        (R ^ (n + 1) / ((n : ℝ) + 1)) * D_S := by
    simpa only [D_S, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hdiscrepancyReal
  refine ⟨w, Dw, hW, hTarget, hraw, hgradient, henergyReal', hdiscrepancyReal', ?_⟩
  intro E D Q e normal v β B W line Ω L A G grid C
  have hSm : MeasurableSet S := MeasurableSet.iInter fun j : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj j).continuous.measurable
  have hrect : ∀ i x, x ∈ S → ∀ t ∈ Ioo (-1 : ℝ) 1,
      Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) ∈
        ball (0 : Domain (n + 1)) R := by
    intro i x hx t ht
    exact unit_coordinate_line_rectangle_mem_ball (p i) x (fun j => mem_iInter.mp hx j) ht
  obtain ⟨offset, hoffset, hweak, hACL, hvertexN, hfiber, henergy, hdiscrepancy, htrace⟩ :=
    exists_grid_translate_original_closed_target_face_joint hR w Dw hW hN hTarget
      k p face hface (fun _ => S) (fun _ => hSm) (fun _ => -1) (fun _ => 1)
      (fun _ => by norm_num) hrect d sampleFace hε
  refine ⟨offset, hoffset, hweak, ?_, hvertexN, ?_, ?_, ?_, htrace⟩
  · intro z l i hy
    obtain ⟨hraw₀, hLp₀, hD₀, hAC₀, hAE₀, hN₀, hinc₀⟩ := hACL z l i hy
    refine ⟨hraw₀, hLp₀, hD₀, hAC₀, hAE₀, ?_, ?_⟩
    · intro t ht
      exact hN₀ t ht
    · intro s hs t ht
      exact coordinatePermACLRepresentative_integral_increments_of_memLp (p i)
        (a := -1) (b := 1) (by norm_num) (w l) (Dw l)
        (β i (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) hD₀ s hs t ht
  · intro j z
    filter_upwards [hfiber j z] with t ht
    dsimp only [A]
    generalize hx : (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset) +
      ∑ s : Fin (d j), t s • EuclideanSpace.single (sampleFace j s) (1 : ℝ)) = x at ht ⊢
    refine ⟨?_, ht.2⟩
    intro l i hy
    obtain ⟨hraw₀, hLp₀, hD₀, hAC₀, hAE₀, hN₀, _hinc₀⟩ := ht.1 l i hy
    refine ⟨hraw₀, hLp₀, hD₀, hAC₀, hAE₀, ?_, ?_⟩
    · intro t ht
      exact hN₀ t ht
    · intro s hs r hr
      exact coordinatePermACLRepresentative_integral_increments_of_memLp (p i)
        (a := -1) (b := 1) (by norm_num) (w l) (Dw l)
        (β i x) hD₀ s hs r hr
  · intro j
    simpa only [henergyReal'] using henergy j
  · intro j
    simpa only [hdiscrepancyReal'] using hdiscrepancy j

end StratificationTheory
