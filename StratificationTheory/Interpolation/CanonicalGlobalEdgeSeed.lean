module

public import StratificationTheory.Interpolation.OriginalGlobalEdgeBase
public import StratificationTheory.Foundation.NativeCoordinateCubeOpen
public import StratificationTheory.Foundation.CubicalSignedPermutations

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Original selected edge data and the literal global vertex chords give
one complete canonical rank-one seed, with the actual inherited vertex-cell
trace classes and paired line-energy budget. -/
theorem exists_canonical_global_edge_seed {n q : ℕ}
    (w : Fin 2 → Domain (n + 1) → Ambient q)
    (Dw : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {Target : Set (Ambient q)} (hTarget : IsClosed Target)
    {ε : ℝ} (hε : 0 < ε) (offset : Fin (n + 1) → ℝ)
    (M : ℝ) (hM : ∀ z ∈ Target, ‖z‖ ≤ M) :
    let p := fun normal : Fin (n + 1) => Equiv.swap (Fin.last n) normal
    let Q := fun normal => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p normal)
    let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := fun normal => p normal (Fin.natAdd n (0 : Fin 1))
    let β := fun normal (y : Domain (n + 1)) => (e₀ ((Q normal).symm y)).1
    let rep := fun l normal => coordinatePermACLRepresentative (p normal) (-1) 1 (w l) (Dw l)
    let line := fun normal x t => Q normal (e₀.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω := fun normal => {y : Domain (n + 1) |
      β normal y ∈ S ∧ (e₀ ((Q normal).symm y)).2 0 ∈ Ioo (-1 : ℝ) 1}
    let L := fun (l : Fin 2) normal (y : Domain (n + 1)) => y ∈ Ω normal →
      rep l normal y = w l y ∧
      MemLp (fun t => w l (line normal (β normal y) t)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      MemLp (fun t => Dw l (line normal (β normal y) t) (j normal)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      AbsolutelyContinuousOnInterval (fun t => rep l normal (line normal (β normal y) t)) (-1) 1 ∧
      (fun t => rep l normal (line normal (β normal y) t)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
        (fun t => w l (line normal (β normal y) t)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, rep l normal (line normal (β normal y) t) ∈ Target) ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
        rep l normal (line normal (β normal y) t) - rep l normal (line normal (β normal y) s) =
          ∫ r in s..t, Dw l (line normal (β normal y) r) (j normal)
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _ : Fin (n + 1) => ε) (fun _ => hε.ne'.isUnit)
    (∀ normal (z : Submodule.span ℤ (Set.range grid)) l,
      L l normal (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) →
    let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (c.val.1 : Fin r → Fin (n + 1))}
    let B := fun r : ℕ => (⟨⋂ i : Fin r, (fun x : Domain r => x i) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_native_coordinate_cube r (-1) 1⟩ : OpenDomain r)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let axis := fun c : Cell 1 => c.val.val.1 0
    let V1 := fun c : Cell 1 => coordinateEdgeUnitMap (p (axis c)) (-1) 1 ε w Dw c.val.val.2
    let D1 := fun c : Cell 1 => coordinateEdgeUnitGradient (p (axis c)) (-1) 1 ε w Dw c.val.val.2
    let point := fun (c : Cell 1) (s : ℝ) => c.val.val.2 + s • EuclideanSpace.single (axis c) (1 : ℝ)
    let A := fun c : Cell 1 => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (point c s) (axis c)‖ ^ 2 + ‖Dw 1 (point c s) (axis c)‖ ^ 2
    let D := fun c : Cell 1 => ∫ s in Ioo (0 : ℝ) ε, ‖w 0 (point c s) - w 1 (point c s)‖ ^ 2
    let Tube := fun c : Cell 1 => D c / ε + Real.sqrt (2 * D c * A c)
    let source1 := fun (c : Cell 1) (x : Domain 1) => c.val.val.2 +
      ∑ a : Fin 1, x a • EuclideanSpace.single (c.val.val.1 a) (1 : ℝ)
    let T1 := fun x : Domain 1 => WithLp.toLp 2 (fun _ : Fin 1 => ε / 2) + (ε / 2) • x
    let U1 := fun (c : Cell 1) (l : Fin 2) => w l ∘ source1 c ∘ T1
    ∀ (child0 : Cell 1 → Fin 1 → Bool → Cell 0)
      (frame0 : Cell 1 → Fin 1 → Equiv.Perm (Fin 1))
      (V0 : Cell 0 → Domain 1 → Ambient q),
    (∀ c i side, (child0 c i side).val.val.2 = c.val.val.2 +
      (if side then ε else 0) • EuclideanSpace.single (c.val.val.1 i) (1 : ℝ)) →
    (∀ c x, V0 c x = rawVertexUnitChord w c.val.val.2 x) →
    ∃ K1 : Cell 1 → Fin 2 → C(Icc (-1 : ℝ) 1,
        Lp (Ambient q) 2 (volume.restrict (B 1).val)),
      (∀ c, MemW12 (B 2) (V1 c) (D1 c)) ∧
      (∀ c, ∀ᵐ x ∂volume.restrict (B 2).val, ‖V1 c x‖ ≤ M) ∧
      (∀ c i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => V1 c (cubicalSignedFaceIsometry 1 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B 1).val),
          K1 c i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V1 c
            (cubicalSignedFaceIsometry 1 i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      (∀ c (side : Bool),
        (K1 c (Fin.last 1) ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict (B 1).val] U1 c (if side then 1 else 0)) ∧
      (∀ c, 0 ≤ Tube c) ∧
      (∀ c, ∀ᵐ x ∂volume.restrict (B 2).val, (infDist (V1 c x) Target) ^ 2 ≤ Tube c) ∧
      (∀ c (i : Fin 1) (side : Bool),
        (K1 c i.castSucc ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict (B 1).val]
          V0 (child0 c i side) ∘ (cubicalSignedPermutation 1 (frame0 c i) (fun _ => true))) ∧
      ∀ c, (∫ x in (B 2).val, hsNormSq (D1 c x)) ≤ (ε / 2) * A c + ε⁻¹ * D c := by
  classical
  intro p Q e₀ j β rep line S Ω L grid hACL Cell B e axis V1 D1 point A D Tube source1 T1 U1
    child0 frame0 V0 hChildOrigin hVertex
  have hProducer := exists_global_original_edge_base w Dw hTarget hε offset M hM
  dsimp only at hProducer
  dsimp only [L, rep] at hACL
  generalize hCanonical : (@coordinatePermACLRepresentative n q) = Rep at hACL hProducer
  with_reducible obtain ⟨hW, hEnergy, hTubeNonneg, hTubeClosed, hNormClosed, K, hRaw, hEnd⟩ := hProducer hACL
  refine ⟨K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_reducible simpa only [V1, D1, p, axis, B, Set.preimage, PiLp.proj_apply] using hW
  · intro c
    filter_upwards [ae_restrict_mem (B 2).property.measurableSet] with x hx
    have h := hNormClosed c x (fun i => ⟨(mem_iInter.mp hx i).1.le, (mem_iInter.mp hx i).2.le⟩)
    with_reducible simpa only [V1, p, axis] using h
  · intro c i
    filter_upwards [hRaw c i] with t ht
    intro hti
    obtain ⟨hs, heq⟩ := ht hti
    let F : Domain 1 → Ambient q := fun x => V1 c (cubicalSignedFaceIsometry 1 i true
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
    have hs' : MemLp F 2 (volume.restrict (B 1).val) := by
      with_reducible simpa only [F, V1, p, axis, B, e, Set.preimage, PiLp.proj_apply] using hs
    refine ⟨hs', ?_⟩
    change K c i ⟨t, hti.1.le, hti.2.le⟩ = hs'.toLp F
    rw [heq]
    apply Lp.ext
    filter_upwards [hs.coeFn_toLp, hs'.coeFn_toLp] with x hx hy
    exact hx.trans ((by rfl : _ = F x).trans hy.symm)
  · intro c side
    have hLast : (Fin.last 1 : Fin 2) ≠ 0 := by decide
    have h := hEnd c (Fin.last 1) side
    rw [if_neg hLast] at h
    exact h
  · intro c
    with_reducible simpa only [Tube, A, D, point, axis] using hTubeNonneg c
  · intro c
    filter_upwards [ae_restrict_mem (B 2).property.measurableSet] with x hx
    have h := hTubeClosed c x (fun i => ⟨(mem_iInter.mp hx i).1.le, (mem_iInter.mp hx i).2.le⟩)
    with_reducible simpa only [V1, p, axis, Tube, A, D, point] using h
  · intro c i side
    have hi : i = 0 := by apply Fin.ext; have := i.isLt; omega
    subst i
    have hSp := hEnd c 0 side
    rw [if_pos rfl] at hSp
    have hFrame (x : Domain 1) : (cubicalSignedPermutation 1 (frame0 c 0) (fun _ => true)) x = x := by
      ext j
      obtain ⟨a, rfl⟩ := (frame0 c 0).surjective j
      rw [cubicalSignedPermutation_apply, if_pos rfl]
      apply congrArg (fun a : Fin 1 => x a)
      apply Fin.ext
      have := a.isLt
      have := ((frame0 c 0) a).isLt
      omega
    filter_upwards [hSp] with x hx
    rw [Function.comp_apply, hFrame, hVertex, hChildOrigin]
    exact hx
  · intro c
    with_reducible simpa only [D1, p, axis, B, A, D, point, Set.preimage, PiLp.proj_apply] using hEnergy c

end StratificationTheory
