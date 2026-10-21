import SymmetricSubgroupAsymptotics.CFSGSymplecticSymmetricShearMembership
import SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixVector

/-! Actual natural nonzero-vector transitivity follows from the
symmetric shear words, without identifying the elementary group with a
larger form-preserving group. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGMatrixShearUnits CFSGSymmetricMatrixVector
variable (K : Type) [Field K]

private theorem upper_mulVec (r : ℕ) (S : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (x y : Fin (r + 1) → K) :
    (upper S : Mat K (r + 1)) *ᵥ Sum.elim x y = Sum.elim (x + S *ᵥ y) y := by
  simp only [upper, Matrix.fromBlocks_mulVec, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]

private theorem lower_mulVec (r : ℕ) (S : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (x y : Fin (r + 1) → K) :
    (lower S : Mat K (r + 1)) *ᵥ Sum.elim x y = Sum.elim x (S *ᵥ x + y) := by
  simp only [lower, Matrix.fromBlocks_mulVec, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

theorem exists_elementary_mulVec_first_basis (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    ∃ g : elementaryRootGroup K (r + 1),
      (g.val : Mat K (r + 1)) *ᵥ Pi.single (Sum.inl (0 : Fin (r + 1))) 1 = v := by
  let e : Fin (r + 1) → K := Pi.single 0 1
  have he : e ≠ 0 := by
    intro h
    have hz := congrFun h 0
    simp [e] at hz
  let x : Fin (r + 1) → K := v ∘ Sum.inl
  let y : Fin (r + 1) → K := v ∘ Sum.inr
  have hvxy : v = Sum.elim x y := by funext i; cases i <;> rfl
  have hbase : (Pi.single (Sum.inl (0 : Fin (r + 1))) (1 : K) : Index (r + 1) → K) = Sum.elim e 0 := by
    funext i
    cases i <;> simp [e, Pi.single_apply]
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      rw [hvxy, hx, hy]
      funext z
      cases z <;> rfl
    obtain ⟨T, hT, hTe⟩ := exists_symmetric_mulVec e y he
    obtain ⟨S, hS, hSy⟩ := exists_symmetric_mulVec y (-e) hy
    let g : elementaryRootGroup K (r + 1) :=
      ⟨upper S * lower T, (elementaryRootGroup K (r + 1)).mul_mem
        (symmetric_upper_mem K r hr S hS) (symmetric_lower_mem K r hr T hT)⟩
    refine ⟨g, ?_⟩
    change ((upper S : Mat K (r + 1)) * (lower T : Mat K (r + 1))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hbase, lower_mulVec, hTe, add_zero, upper_mulVec,
      hSy, add_neg_cancel, hvxy, hx]
  · obtain ⟨T, hT, hTe⟩ := exists_symmetric_mulVec e e he
    obtain ⟨S, hS, hSe⟩ := exists_symmetric_mulVec e (x - e) he
    obtain ⟨R, hR, hRx⟩ := exists_symmetric_mulVec x (y - e) hx
    let g : elementaryRootGroup K (r + 1) :=
      ⟨lower R * upper S * lower T, (elementaryRootGroup K (r + 1)).mul_mem
        ((elementaryRootGroup K (r + 1)).mul_mem
          (symmetric_lower_mem K r hr R hR) (symmetric_upper_mem K r hr S hS))
        (symmetric_lower_mem K r hr T hT)⟩
    refine ⟨g, ?_⟩
    change (((lower R : Mat K (r + 1)) * (upper S : Mat K (r + 1))) *
      (lower T : Mat K (r + 1))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hbase, lower_mulVec,
      hTe, add_zero, upper_mulVec, hSe]
    have hx' : e + (x - e) = x := by abel
    rw [hx', lower_mulVec, hRx, sub_add_cancel, ← hvxy]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
