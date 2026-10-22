import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharacterDiagonal

/-! Exact character scaling on an actual Weyl-conjugate root family.
No identification of that family from its degree is used: both sides
retain the original conjugating matrix word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckConjugateCharacter
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckCharacterDiagonal
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem conjugate_root_scaling (K : Type) [Field K] (f : (n→ℤ)→ₗ[ℤ]ℤ)
    (t : Kˣ) (w : List (Fin r)) (i : Fin r) (a : K) :
    characterDiagonal A hs hp b K f t*
      (wordUnit A hs hp b s K w*canonicalRoot (realizationData A hs hp b s) K false i a*
        (wordUnit A hs hp b s K w)⁻¹)*(characterDiagonal A hs hp b K f t)⁻¹=
      wordUnit A hs hp b s K w*
        canonicalRoot (realizationData A hs hp b s) K false i
          (a*(t:K)^(f (wordLinear A hs hp b s w (s i:Roots A).val)))*
        (wordUnit A hs hp b s K w)⁻¹ := by
  let e := wordLinear A hs hp b s w
  let d := characterDiagonal A hs hp b K (f.comp e.toLinearMap) t
  let u := wordUnit A hs hp b s K w
  have hf : (f.comp e.toLinearMap).comp e.symm.toLinearMap=f := by
    ext x
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  have hd : u*d*u⁻¹=characterDiagonal A hs hp b K f t := by
    dsimp only [u,d,e]
    rw [word_conjugate_character]
    change characterDiagonal A hs hp b K
      ((f.comp e.toLinearMap).comp e.symm.toLinearMap) t=characterDiagonal A hs hp b K f t
    rw [hf]
  rw [←hd]
  calc
    _=u*(d*canonicalRoot (realizationData A hs hp b s) K false i a*d⁻¹)*u⁻¹ := by
      dsimp only [u]
      group
    _=u*canonicalRoot (realizationData A hs hp b s) K false i
      (a*(t:K)^(f (e (s i:Roots A).val)))*u⁻¹ := by
      exact congrArg (fun v=>u*v*u⁻¹)
        (character_conjugate_positive A hs hp b s K (f.comp e.toLinearMap) t i a)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckConjugateCharacter
