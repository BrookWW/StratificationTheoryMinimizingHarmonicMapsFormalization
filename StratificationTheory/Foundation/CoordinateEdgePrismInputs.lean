module

public import StratificationTheory.Foundation.CoordinateEdgeLocalData

/-!
# Original coordinate edge data in a literal square parameterization

A pointwise identified source parameterization transports the original
line classes, original gradient column, closed target and raw vertices to
the actual edge functions used by a square-prism connector.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Every analytic qualification comes from the original full coordinate
line. The extra premises are whole-carrier formulas for the same actual
edge parameterization and its raw data. -/
theorem coordinate_edge_prism_inputs {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (y : Domain (n + 1))
    {a b ε : ℝ} (hε : 0 < ε)
    (u R : Domain (n + 1) → Ambient q) (Du : Domain (n + 1) → Gradient (n + 1) q)
    (γ : ℝ → Domain (n + 1)) (F f g : ℝ → Ambient q) {N : Set (Ambient q)} :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := (e (Q.symm y)).1
    let line := fun t => Q (e.symm (β, EuclideanSpace.single (0 : Fin 1) t))
    (∀ s, γ s = y + s • v) →
    (∀ s, F s = R (γ s)) → (∀ s, f s = u (γ s)) → (∀ s, g s = Du (γ s) j) →
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
      F =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f ∧
      (∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
        F t - F s = ∫ r in s..t, g r) ∧
      (∀ s ∈ Icc (0 : ℝ) ε, F s ∈ N) ∧
      ∀ positive : Bool, F (if positive then ε else 0) = f (if positive then ε else 0) := by
  intro Q e j v β line hγ hF hf hg ha hb hU hD hAE hValues hInc hRaw₀ hRawε
  obtain ⟨hfl, hgl, _hAC, hAEl, hValuesl, _hTarget, hIncl, _hR₀, _hRε⟩ :=
    coordinate_edge_original_local_data (n := n) (q := q) p y hε
      (u := u) (R := R) (Du := Du) (N := N) ha hb hU hD hAE hValues hInc hRaw₀ hRawε
  have hFfun : (fun s => R (y + s • v)) = F :=
    funext fun s => (congrArg R (hγ s)).symm.trans (hF s).symm
  have hffun : (fun s => u (y + s • v)) = f :=
    funext fun s => (congrArg u (hγ s)).symm.trans (hf s).symm
  have hgfun : (fun s => Du (y + s • v) j) = g :=
    funext fun s => (congrArg (fun z => Du z j) (hγ s)).symm.trans (hg s).symm
  rw [hffun] at hfl
  rw [hgfun] at hgl
  rw [hFfun, hffun] at hAEl
  refine ⟨hfl, hgl, hAEl, ?_, ?_, ?_⟩
  · intro s hs t ht
    rw [← congrFun hFfun t, ← congrFun hFfun s, ← hgfun]
    exact hIncl s hs t ht
  · intro s hs
    rw [← congrFun hFfun s]
    exact hValuesl s hs
  · intro positive
    cases positive
    · rw [hF, hf, hγ]
      simpa only [Bool.false_eq_true, ite_false, zero_smul, add_zero] using hRaw₀
    · rw [hF, hf, hγ]
      exact hRawε

end StratificationTheory
