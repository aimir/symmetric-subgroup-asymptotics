import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute

/-! A Weyl-conjugated positive simple parameter commutes with another
positive simple parameter when their actual lattice pairing is zero or
one. Every matrix expression uses one and the same realization datum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootCommute
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateRootSubgroupCommute
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem positive_word_commute_simple (K : Type) [Field K] (w : List (Fin r))
    (i j : Fin r)
    (hpair : integerPairing A (wordRoot A hs hp b₀ s₀ w (s₀ i)).val (s₀ j : Roots A).val=0 ∨
      integerPairing A (wordRoot A hs hp b₀ s₀ w (s₀ i)).val (s₀ j : Roots A).val=1)
    (a b : K) :
    Commute (canonicalWord D K w*canonicalRoot D K false i a*(canonicalWord D K w)⁻¹)
      (canonicalRoot D K false j b) :=
  rootSubgroup_pair_commute A hd hs hp ho K _ _ hpair _ _
    (positive_word_mem_rootSubgroup A hd hs hp ho K w i a)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K j b)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootCommute
