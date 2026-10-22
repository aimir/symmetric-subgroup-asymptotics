import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCollectingCoefficient
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction

/-! The original simple brackets have their literal sum degree; an
adjacent bracket is nonzero over EVERY field because it is actual Weyl
conjugation of a primitive simple operator. No structure constant is
cancelled after reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleBracketDegrees
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGNormTwoGeckSimpleRootCoordinates CFSGNormTwoGeckWeylCollectingCoefficient
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s
local notation "ell" => latticeWeight A hs hp b

theorem simple_bracket_support (K : Type) [Field K] (i j : Fin r) :
    Supported ell (fun v=>v+((s i:Roots A).val+(s j:Roots A).val))
      ⁅fieldRoot D K false i,fieldRoot D K false j⁆ := by
  have hij := supported_mul (field_E_lattice_support A hs hp b s K i)
    (field_E_lattice_support A hs hp b s K j)
  have hji := supported_mul (field_E_lattice_support A hs hp b s K j)
    (field_E_lattice_support A hs hp b s K i)
  have hpij : Supported ell (fun v=>v+((s i:Roots A).val+(s j:Roots A).val))
      (fieldRoot D K false i*fieldRoot D K false j) := by
    apply supported_congr hij
    intro v
    dsimp only [Function.comp_apply]
    abel
  have hpji : Supported ell (fun v=>v+((s i:Roots A).val+(s j:Roots A).val))
      (fieldRoot D K false j*fieldRoot D K false i) := by
    apply supported_congr hji
    intro v
    dsimp only [Function.comp_apply]
    abel
  intro k l hkl
  rw [Ring.lie_def,Matrix.sub_apply,hpij k l hkl,hpji k l hkl,sub_self]

theorem adjacent_bracket_ne_zero (K : Type) [Field K] (i j : Fin r)
    (hij : cartan b s i j= -1) :
    ⁅fieldRoot D K false i,fieldRoot D K false j⁆≠0 := by
  intro hz
  have hconj := weyl_conjugate_adjacent_all_rings A hs hp b s K i j hij
  rw [hz] at hconj
  have hE : fieldRoot D K false j=0 := by
    apply (CFSGAlgebraConjugationAction.action K
      (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) (canonicalWeyl D K i)).injective
    simpa only [CFSGAlgebraConjugationAction.action_apply,map_zero] using hconj
  have he := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K=>
    M (Sum.inl (s j)) (Sum.inr (CFSGNormTwoGeckColumns.negativeIndex A hs hp (s j)))) hE
  dsimp only at he
  rw [field_E_unit_entry] at he
  exact one_ne_zero he

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleBracketDegrees
