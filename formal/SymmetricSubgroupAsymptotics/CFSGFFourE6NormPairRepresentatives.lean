import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormImage
import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu
import Mathlib.SetTheory.Cardinal.Finite

/-! A selected 2+24 representative pilot for the actual E6 diagram
involution. The root tests run only on the pinned complete 72-root menu;
no reduction over the general Roots Fintype occurs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormPairRepresentatives
open CFSGIntegerMatrixPairing

def twistVector (x:Fin 6→ℤ) : Fin 6→ℤ := fun i=>x (CFSG.Models.e6Twist i)

def cartanRepresentative : Fin 2→Fin 6 := ![0,2]

def rootRepresentatives : Finset (Fin 6→ℤ) := CFSGE6FiniteRootMenu.menu.filter
  (fun x=>x 0<x 5 ∨ x 0=x 5 ∧ x 2<x 4)

theorem cartanRepresentative_injective : Function.Injective cartanRepresentative := by decide +kernel

theorem cartanRepresentative_disjoint : ∀i j:Fin 2,
    cartanRepresentative i≠CFSG.Models.e6Twist (cartanRepresentative j) := by decide +kernel

theorem cartanRepresentative_cover : ∀i:Fin 6,CFSG.Models.e6Twist i=i ∨
    ∃j:Fin 2,i=cartanRepresentative j∨i=CFSG.Models.e6Twist (cartanRepresentative j) := by decide +kernel

theorem rootRepresentatives_card : rootRepresentatives.card=24 := by decide +kernel

theorem rootRepresentatives_norm : ∀x∈rootRepresentatives,
    integerPairing CartanMatrix.E₆ x x=2 := by decide +kernel

theorem rootRepresentatives_disjoint : ∀x∈rootRepresentatives,∀y∈rootRepresentatives,
    x≠twistVector y := by decide +kernel

theorem rootRepresentatives_cover : ∀x∈CFSGE6FiniteRootMenu.menu,
    twistVector x=x ∨ x∈rootRepresentatives ∨ twistVector x∈rootRepresentatives := by decide +kernel

noncomputable section
open scoped Classical
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases

def PairIndex := Fin 2⊕rootRepresentatives

theorem pairIndex_card : Nat.card PairIndex=26 := by
  change Nat.card (Fin 2⊕rootRepresentatives)=26
  rw [Nat.card_sum]
  simp only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin,Fintype.card_coe,rootRepresentatives_card]

def selectedRepresentative : PairIndex→GeckIndex
  | .inl i=>.inl (E6Index (cartanRepresentative i))
  | .inr r=>.inr ⟨r.val,rootRepresentatives_norm r.val r.property⟩

end
end SymmetricSubgroupAsymptotics.CFSGFFourE6NormPairRepresentatives
