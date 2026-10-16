module

public import StratificationTheory.Foundation.UniformGridUnitCellTransport
public import StratificationTheory.Foundation.CoordinateCellParameterInjectivity

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- The original physical source cap is recovered on the whole base by
the same inverse unit-cell spatial normalization. -/
theorem canonical_prism_physical_cap_inverse {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (base lo x : Domain m) :
    let h := ε / 2
    let F : Domain m → Domain m := fun y => h⁻¹ • (y - (lo + WithLp.toLp 2 (fun _ => h)))
    (base + lo) + ∑ j : Fin m, (h + h * F x j) • EuclideanSpace.single j (1 : ℝ) =
      base + x := by
  intro h F
  ext j
  have hj := coordinate_cell_affine_parameter_coordinate
    (Function.Embedding.refl (Fin m)) (base + lo) h h (F x) j
  simp only [Function.Embedding.refl_apply] at hj
  rw [hj]
  change base j + lo j + h + h * (h⁻¹ * (x j - (lo j + h))) = base j + x j
  rw [← mul_assoc, mul_inv_cancel₀ (half_pos hε).ne', one_mul]
  ring

/-- The actual temporal unit curve of one selected cell yields its native
physical-cell curve, with both original source values as endpoint classes. -/
theorem exists_canonical_prism_physical_temporal_trace {m L q : ℕ}
    {ε : ℝ} (hε : 0 < ε) (hL : 0 < L) (α : Fin m → Fin L)
    (base origin : Domain m)
    (hOrigin : origin = base + WithLp.toLp 2 (fun j => ((α j).val : ℝ) * ε))
    (w : Fin 2 → Domain m → Ambient q)
    (V : Domain (m + 1) → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)
    let S := ⋂ j : Fin m, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let z : Fin (m + 1) → Fin L := Fin.snoc α (⟨0, hL⟩ : Fin L)
    let lo : Domain (m + 1) := WithLp.toLp 2 (fun j => ((z j).val : ℝ) * ε)
    let T := fun y : Domain (m + 1) => (ε / 2)⁻¹ •
      (y - (lo + WithLp.toLp 2 (fun _ => ε / 2)))
    let Q := cubicalSignedFaceIsometry m (Fin.last m) true
    let cap := fun (side : Bool) (x : Domain m) =>
      w (if side then 1 else 0) (origin + ∑ j : Fin m,
        (ε / 2 + (ε / 2) * x j) • EuclideanSpace.single j (1 : ℝ))
    ∀ H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain m => V (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ side, (H ⟨if side then 1 else -1, by cases side <;> norm_num,
      by cases side <;> norm_num⟩ : Domain m → Ambient q) =ᵐ[volume.restrict S] cap side) →
    ∃ K : C(Icc (0 : ℝ) ε,
      Lp (Ambient q) 2 (volume.restrict (uniformGridCell m L ε α).val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
        ∃ hs : MemLp (fun x : Domain m => V (T (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2
          (volume.restrict (uniformGridCell m L ε α).val),
          K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (T (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ((K ⟨0, le_rfl, hε.le⟩ : Domain m → Ambient q)
        =ᵐ[volume.restrict (uniformGridCell m L ε α).val] fun x => w 0 (base + x)) ∧
      ((K ⟨ε, hε.le, le_rfl⟩ : Domain m → Ambient q)
        =ᵐ[volume.restrict (uniformGridCell m L ε α).val] fun x => w 1 (base + x)) := by
  intro e S z lo T Q cap H hRaw hCap
  let spatialLo : Domain m := WithLp.toLp 2 (fun j => ((α j).val : ℝ) * ε)
  let F := fun x : Domain m => (ε / 2)⁻¹ •
    (x - (spatialLo + WithLp.toLp 2 (fun _ => ε / 2)))
  have hQ (x : Domain (m + 1)) : cubicalSignedFaceIsometry m (Fin.last m) true x = x := by
    ext j
    have hj := cubicalSignedFaceIsometry_apply (Fin.last m) true x j
    simpa only [Equiv.swap_self, Equiv.refl_apply, ite_true, ite_self] using hj
  have hSet : (⋂ j : Fin m, (EuclideanSpace.proj j) ⁻¹'
      Ioo (spatialLo j) (spatialLo j + ε)) = (uniformGridCell m L ε α).val := by
    ext x
    rw [mem_uniformGridCell_iff]
    simp only [mem_iInter, mem_preimage]
    apply forall_congr'
    intro j
    change x j ∈ Ioo (((α j).val : ℝ) * ε) (((α j).val : ℝ) * ε + ε) ↔ _
    have hHi : (((α j).val : ℝ) + 1) * ε = ((α j).val : ℝ) * ε + ε := by ring
    rw [hHi]
  have hCurve := exists_translated_cube_L2_trace_denormalization hε spatialLo 0
    (fun p : Domain m × ℝ => V (Q (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))))
    (cap false) (cap true) H hRaw (hCap false) (hCap true)
  dsimp only at hCurve
  rw [hSet] at hCurve
  obtain ⟨K, hK, hK₀, hK₁, _hUnique⟩ := hCurve
  have hNormal (x : Domain m) (t : ℝ) :
      T (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
        Q (e.symm (F x, EuclideanSpace.single (0 : Fin 1) (t / (ε / 2) - 1))) := by
    have hh := inverse_translated_cube_face_coordinates hε lo (Fin.last m) x t
    simpa only [T, F, spatialLo, e, Q, hQ, Equiv.swap_self, Equiv.refl_apply, z, lo, Fin.snoc_castSucc,
      Fin.snoc_last, Nat.cast_zero, zero_mul, sub_zero] using hh
  have hEnd (side : Bool) (x : Domain m) : cap side (F x) =
      w (if side then 1 else 0) (base + x) := by
    dsimp only [cap]
    rw [hOrigin]
    exact congrArg (w (if side then 1 else 0))
      (canonical_prism_physical_cap_inverse hε base spatialLo x)
  dsimp only [F] at hNormal
  have hτmem (t : Icc (0 : ℝ) ε) : t.val ∈ Icc (0 : ℝ) (0 + ε) := by
    simpa only [zero_add] using t.property
  let τ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) (0 + ε)) :=
    ⟨fun t => ⟨t.val, hτmem t⟩, continuous_subtype_val.subtype_mk hτmem⟩
  refine ⟨K.comp τ, ?_, ?_, ?_⟩
  · filter_upwards [hK] with t ht htI
    obtain ⟨hs, hClass⟩ := ht (by simpa only [zero_add] using htI)
    change ∃ hs : MemLp (fun x : Domain m => V (T (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2
        (volume.restrict (uniformGridCell m L ε α).val),
      K ⟨t, τ ⟨t, htI.1.le, htI.2.le⟩ |>.property⟩ = hs.toLp _
    simpa only [sub_zero, ← hNormal] using (show ∃ hs, K ⟨t, _⟩ = hs.toLp _ from ⟨hs, hClass⟩)
  · change (K (τ ⟨0, le_rfl, hε.le⟩) : Domain m → Ambient q) =ᵐ[_] _
    exact hK₀.trans (Eventually.of_forall fun x => hEnd false x)
  · have hτ₁ : τ ⟨ε, hε.le, le_rfl⟩ =
        ⟨0 + ε, by linarith, le_rfl⟩ := by
      apply Subtype.ext
      simp only [τ, ContinuousMap.coe_mk, zero_add]
    change (K (τ ⟨ε, hε.le, le_rfl⟩) : Domain m → Ambient q) =ᵐ[_] _
    rw [hτ₁]
    exact hK₁.trans (Eventually.of_forall fun x => hEnd true x)

end StratificationTheory
