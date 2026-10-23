import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCenter
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRoot
import SymmetricSubgroupAsymptotics.CFSGMatrixConjugateDisplacement

/-! The displacement of each nonidentity ACTUAL central root has the
same natural centre line. Literal conjugation transports that line to
the first-column line. These are natural matrix statements, not an
assumed automorphism or polar-space recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical

theorem single_mulVec_range {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (i j : I) (a : K) (ha : a ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (Matrix.single i j a)) =
      K ∙ (Pi.single i (1 : K) : I → K) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.single_mulVec]
    change (Pi.single i (a * x j) : I → K) ∈ K ∙ (Pi.single i (1 : K) : I → K)
    have he : Pi.single i (a * x j) =
        (a * x j) • (Pi.single i (1 : K) : I → K) := by
      funext k
      by_cases hk : k = i <;> simp [Pi.single_apply, hk]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    intro y hy
    have he : y = (Pi.single i (1 : K) : I → K) := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨Pi.single j a⁻¹, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.single_mulVec]
    change (Pi.single i (a * (Pi.single j a⁻¹ : I → K) j) : I → K) = Pi.single i 1
    simp only [Pi.single_eq_same, mul_inv_cancel₀ ha]

def centralPoint (q : CFSG.PrimePower) (s : ℕ) :
    Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2) :=
  (q.Extension 2) ∙ (Pi.single (0 : Fin (s + 3)) 1)

def conjugateCentralPoint (q : CFSG.PrimePower) (s : ℕ) (g : naturalFixed (s + 2) q) :
    Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2) :=
  (centralPoint q s).map (Matrix.mulVecLin (g.val.val : Mat (q.Extension 2) (s + 2)))

theorem centralFixed_displacement_range (q : CFSG.PrimePower) (s : ℕ)
    (b : q.Extension 2) (hb : Condition q s 0 b) (hb0 : b ≠ 0) :
    LinearMap.range (Matrix.mulVecLin
      (((centralFixed q s b hb).val.val : Mat (q.Extension 2) (s + 2)) - 1)) =
      centralPoint q s := by
  rw [show ((centralFixed q s b hb).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) b from
    radicalCentral_matrix q s b hb, add_sub_cancel_left]
  exact single_mulVec_range 0 (Fin.last (s + 2)) b hb0

theorem conjugateCentralFixed_displacement_range (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) (b : q.Extension 2)
    (hb : Condition q s 0 b) (hb0 : b ≠ 0) :
    LinearMap.range (Matrix.mulVecLin
      (((g * centralFixed q s b hb * g⁻¹).val.val : Mat (q.Extension 2) (s + 2)) - 1)) =
      conjugateCentralPoint q s g := by
  change LinearMap.range (Matrix.mulVecLin
    (((g.val.val * (centralFixed q s b hb).val.val * g.val.val⁻¹ :
      (Mat (q.Extension 2) (s + 2))ˣ) : Mat (q.Extension 2) (s + 2)) - 1)) = _
  rw [CFSGMatrixConjugateDisplacement.conjugate_sub_one,
    CFSGMatrixConjugateDisplacement.conjugate_range, centralFixed_displacement_range q s b hb hb0]
  rfl

theorem conjugateCentralPoint_eq_of_element_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 2) q) (b c : q.Extension 2)
    (hb : Condition q s 0 b) (hc : Condition q s 0 c) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (he : g * centralFixed q s b hb * g⁻¹ = h * centralFixed q s c hc * h⁻¹) :
    conjugateCentralPoint q s g = conjugateCentralPoint q s h := by
  have hm := congrArg (fun u : naturalFixed (s + 2) q =>
    LinearMap.range (Matrix.mulVecLin ((u.val.val : Mat (q.Extension 2) (s + 2)) - 1))) he
  simpa only [conjugateCentralFixed_displacement_range q s g b hb hb0,
    conjugateCentralFixed_displacement_range q s h c hc hc0] using hm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
