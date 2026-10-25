import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootOrders

/-! Actual additive parameter homomorphisms for the relative D source.
The two terminal roots commute in every characteristic, so their
Frobenius-paired product is additive in the full extension parameter.
These are homomorphisms into the literal relative-root subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeParameterHoms
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGTwistedDRelativeElementaryGroup CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField CFSGTwistedDSingularPrefix

private theorem root_zero (K : Type) [CommRing K] (r : ℕ) (neg : Bool) (i : Fin r) :
    rootTransvection K r neg i 0 = 1 :=
  congrArg Subtype.val (rootElement_zero K r neg i)

private theorem root_add (K : Type) [CommRing K] (r : ℕ) (neg : Bool)
    (i : Fin r) (a b : K) :
    rootTransvection K r neg i (a+b) =
      rootTransvection K r neg i a * rootTransvection K r neg i b :=
  congrArg Subtype.val (rootElement_add K r neg i a b)

theorem pairedRoot_zero (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) :
    pairedRoot n q neg 0 = 1 := by
  rw [pairedRoot, map_zero, root_zero, root_zero, mul_one]

theorem pairedRoot_add (n : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (a b : q.Extension 2) :
    pairedRoot n q neg (a+b) = pairedRoot n q neg a * pairedRoot n q neg b := by
  have hc := CFSGOrthogonalDTerminalRootCommutation.rootTransvection_commute
    (q.Extension 2) n neg neg b (definingFieldAutomorphism q 2 a)
  dsimp only [pairedRoot]
  rw [map_add, root_add, root_add]
  exact hc.mul_mul_mul_comm _ _

def chainParameterHom (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) (i : Fin n) :
    Multiplicative (fixedField q) →* relativeRootGroup n q where
  toFun a := ⟨rootTransvection (q.Extension 2) (n+2) neg (chainNode n i)
    (a.toAdd : q.Extension 2), chain_mem n q neg i a.toAdd⟩
  map_one' := Subtype.ext (root_zero _ _ _ _)
  map_mul' a b := by
    apply Subtype.ext
    exact root_add _ _ _ _ _ _

def pairedParameterHom (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) :
    Multiplicative (q.Extension 2) →* relativeRootGroup n q where
  toFun a := ⟨pairedRoot n q neg a.toAdd, paired_mem n q neg a.toAdd⟩
  map_one' := Subtype.ext (pairedRoot_zero n q neg)
  map_mul' a b := Subtype.ext (pairedRoot_add n q neg a.toAdd b.toAdd)

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeParameterHoms
