import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear

/-! The actual paired matrix/lattice Weyl-word subgroup. Its definition
retains a literal common word witness, so it requires no claim that the
coefficient-field matrix determines its integral lattice action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLiftedWeylWords
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

abbrev Pair (K : Type) [Field K] :=
  (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ × ((n→ℤ)≃ₗ[ℤ](n→ℤ))

def wordPair (K : Type) [Field K] (w : List (Fin r)) : Pair A hs hp b K :=
  (wordUnit A hs hp b s K w,wordLinear A hs hp b s w)

theorem wordPair_append (K : Type) [Field K] (v w : List (Fin r)) :
    wordPair A hs hp b s K (v++w)=wordPair A hs hp b s K v*wordPair A hs hp b s K w := by
  apply Prod.ext
  · exact wordUnit_append A hs hp b s K v w
  · exact wordLinear_append A hs hp b s v w

theorem wordPair_inverseWord (K : Type) [Field K] (w : List (Fin r)) :
    wordPair A hs hp b s K (inverseWord w)=(wordPair A hs hp b s K w)⁻¹ := by
  apply Prod.ext
  · exact wordUnit_inverseWord A hs hp b s K w
  · exact wordLinear_inverseWord A hs hp b s w

def liftedWeyl (K : Type) [Field K] : Subgroup (Pair A hs hp b K) where
  carrier := {x | ∃w : List (Fin r),wordPair A hs hp b s K w=x}
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro x y ⟨v,rfl⟩ ⟨w,rfl⟩
    exact ⟨v++w,wordPair_append A hs hp b s K v w⟩
  inv_mem' := by
    rintro x ⟨w,rfl⟩
    exact ⟨inverseWord w,wordPair_inverseWord A hs hp b s K w⟩

theorem wordPair_mem_liftedWeyl (K : Type) [Field K] (w : List (Fin r)) :
    wordPair A hs hp b s K w∈liftedWeyl A hs hp b s K := ⟨w,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLiftedWeylWords
