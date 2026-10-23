import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation

/-! Each actual relative-root generator has defining-prime power one.
This follows from literal root additivity and terminal commutation; no
p-subgroup or Sylow identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootOrders
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGTwistedDRelativeElementaryGroup CFSGOrthogonalDGenerationForkTorus

theorem rootElement_pow (K : Type) [CommRing K] (r : ℕ) (neg : Bool) (i : Fin r)
    (a : K) (m : ℕ) : (rootElement K r neg i a) ^ m = rootElement K r neg i (m • a) := by
  induction m with
  | zero => rw [pow_zero, zero_nsmul, rootElement_zero]
  | succ m ih => rw [pow_succ, ih, ← rootElement_add, succ_nsmul]

theorem rootTransvection_pow_char (K : Type) [CommRing K] (p : ℕ) [CharP K p]
    (r : ℕ) (neg : Bool) (i : Fin r) (a : K) :
    (rootTransvection K r neg i a) ^ p = 1 := by
  have hp : p • a = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero K p, zero_mul]
  have h := congrArg Subtype.val (rootElement_pow K r neg i a p)
  simpa only [Subgroup.coe_pow, hp, rootElement_zero, Subgroup.coe_one] using h

theorem pairedRoot_pow_prime (n : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (a : q.Extension 2) : (pairedRoot n q neg a) ^ q.prime = 1 := by
  have hc := CFSGOrthogonalDTerminalRootCommutation.rootTransvection_commute
    (q.Extension 2) n neg neg a (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 a)
  rw [pairedRoot, hc.mul_pow, rootTransvection_pow_char (q.Extension 2) q.prime,
    rootTransvection_pow_char (q.Extension 2) q.prime, mul_one]

theorem relative_generator_pow_prime (n : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (q.Extension 2) (n + 2))ˣ) (hg : g ∈ relativeGenerators n q) :
    g ^ q.prime = 1 := by
  rcases hg with ⟨neg, i, a, rfl⟩ | ⟨neg, a, rfl⟩
  · exact rootTransvection_pow_char (q.Extension 2) q.prime _ _ _ _
  · exact pairedRoot_pow_prime n q neg a

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootOrders
