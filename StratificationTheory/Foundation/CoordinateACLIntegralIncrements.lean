module

public import StratificationTheory.Foundation.CoordinateGridCompatibility

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The literal canonical coordinate representative has the original
derivative increments whenever that original line derivative is in L2. -/
theorem coordinatePermACLRepresentative_integral_increments_of_memLp
    {n q : ℕ} (p : Equiv.Perm (Fin (n + 1))) {a b : ℝ} (hab : a ≤ b)
    (u : Domain (n + 1) → Ambient q) (Du : Domain (n + 1) → Gradient (n + 1) q)
    (x : Domain n) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c := fun t => Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    MemLp (fun t => Du (c t) (p (Fin.natAdd n (0 : Fin 1))))
      2 (volume.restrict (Ioo a b)) →
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      coordinatePermACLRepresentative p a b u Du (c t) -
        coordinatePermACLRepresentative p a b u Du (c s) =
          ∫ r in s..t, Du (c r) (p (Fin.natAdd n (0 : Fin 1))) := by
  intro Q e c hD s hs t ht
  let U : Domain n × ℝ → Ambient q := fun z =>
    u (Q (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2)))
  let G : Domain n × ℝ → Ambient q := fun z =>
    Du (Q (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2))) (p (Fin.natAdd n (0 : Fin 1)))
  have hline (r : ℝ) : coordinatePermACLRepresentative p a b u Du (c r) =
      fiberACLRepresentative a b U G (x, r) := by
    change fiberACLRepresentative a b U G
      ((e (Q.symm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))))).1,
        (e (Q.symm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))))).2 0) = _
    rw [Q.symm_apply_apply, e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
  rw [hline t, hline s]
  change (_ + ∫ r in a..t, G (x, r)) - (_ + ∫ r in a..s, G (x, r)) = _
  rw [add_sub_add_left_eq_sub]
  have hi := intervalIntegrable_of_memLp_two hab hD
  have hat : IntervalIntegrable (fun r => G (x, r)) volume a t :=
    hi.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
  have has : IntervalIntegrable (fun r => G (x, r)) volume a s :=
    hi.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le hs.1] using Icc_subset_Icc le_rfl hs.2)
  exact intervalIntegral.integral_interval_sub_left hat has

end StratificationTheory
