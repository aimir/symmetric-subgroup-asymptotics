import SymmetricSubgroupAsymptotics.CFSGTwistedDA2MatrixWitness

/-! Two literal double-commutator identities in the natural D chain.
They express either edge of a three-coordinate path without division or
any restriction on the field characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDChainDoubleCommutators
open CFSGTwistedDA2MatrixWitness
variable (K : Type) [Field K] (r : ℕ)

theorem first_edge (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a : K) :
    ⁅⁅chain K r i j hij a, chain K r j k hjk 1⁆,
      chain K r k j (Ne.symm hjk) 1⁆ = chain K r i j hij a := by
  rw [chain_commutator K r i j k hij hjk hik a 1,
    chain_commutator K r i k j hik (Ne.symm hjk) hij (a * 1) 1]
  simp only [mul_one]

theorem second_edge (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a : K) :
    ⁅chain K r j i (Ne.symm hij) 1,
      ⁅chain K r i j hij 1, chain K r j k hjk a⁆⁆ = chain K r j k hjk a := by
  rw [chain_commutator K r i j k hij hjk hik 1 a,
    chain_commutator K r j i k (Ne.symm hij) hik hjk 1 (1 * a)]
  simp only [one_mul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDChainDoubleCommutators
