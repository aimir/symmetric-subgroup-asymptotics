import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterRootSteps

/-! The actual parameterized Weyl word on every two-root string and
every pairing-zero root. These are identities of the original integral
quadratic matrices, including in the bad characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeylPairs
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoRootStrings CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterRootSteps CFSGNormTwoGeckParameterizedWeyl
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem parameterWeyl_pair (K : Type*) [Field K] (i : Fin r) (j k : Roots A) (t : Kˣ)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        (t:K) • Pi.single (.inr k) 1 ∧
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr k) 1=
        (-(t:K)⁻¹) • Pi.single (.inr j) 1 := by
  have hjp := pairing_of_root_add A hs hp hk
  have hkp : integerPairing A (s i:Roots A).val k.val=1 :=
    pairing_of_root_sub A hs hp (i:=(s i:Roots A)) (j:=k) (k:=j) (by rw [hk]; abel)
  have hUk : ∀a : K, rootOperator A hs hp b s K false i a
      (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
    intro a
    exact positive_fixed_of_pairing A hs hp b s K i k a (by omega) (by omega)
  have hVj : ∀a : K, rootOperator A hs hp b s K true i a
      (Pi.single (.inr j) 1)=Pi.single (.inr j) 1 := by
    intro a
    exact negative_fixed_of_pairing A hs hp b s K i j a (by omega) (by omega)
  have hh := CFSGQuadraticWeylParameterStrings.word_pair
    (rootOperator A hs hp b s K false i) (rootOperator A hs hp b s K true i) t
    (Pi.single (.inr j) 1) (Pi.single (.inr k) 1)
    (fun a=>positive_add_of_root A hs hp b s K i j k a hk) hUk hVj
    (fun a=>negative_sub_of_root A hs hp b s K i j k a hk)
  constructor
  · change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)) (Pi.single (.inr j) 1)=_
    rw [parameterWeyl_operator]
    exact hh.1
  · change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)) (Pi.single (.inr k) 1)=_
    rw [parameterWeyl_operator]
    exact hh.2

theorem parameterWeyl_fixed (K : Type*) [Field K] (i : Fin r) (j : Roots A) (t : Kˣ)
    (hj : integerPairing A (s i:Roots A).val j.val=0) :
    (parameterWeyl A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        Pi.single (.inr j) 1 := by
  have hU : ∀a : K, rootOperator A hs hp b s K false i a
      (Pi.single (.inr j) 1)=Pi.single (.inr j) 1 := by
    intro a
    exact positive_fixed_of_pairing A hs hp b s K i j a (by omega) (by omega)
  have hV : ∀a : K, rootOperator A hs hp b s K true i a
      (Pi.single (.inr j) 1)=Pi.single (.inr j) 1 := by
    intro a
    exact negative_fixed_of_pairing A hs hp b s K i j a (by omega) (by omega)
  change (Matrix.toLinAlgEquiv' (parameterWeyl A hs hp b s K i t : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)) (Pi.single (.inr j) 1)=_
  rw [parameterWeyl_operator]
  exact CFSGQuadraticWeylParameterStrings.word_fixed _ _ t _ hU hV

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeylPairs
