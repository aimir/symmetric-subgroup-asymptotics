import SymmetricSubgroupAsymptotics.AbelianExtensionCommutingFibres
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The actual nonsplit abelian-extension class comparison.
Joint commuting-pair fibres over EVERY pair in the original quotient
are compared to the associated split extension and then summed. Equal
actual group orders cancel. No character theory or splitting premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianExtensionClassComparison
open AbelianExtensionConjugation AbelianExtensionCommutingFibres
variable {G:Type*} [Group G] [Finite G] (N:Subgroup G) [N.Normal] [IsMulCommutative N]

theorem commuting_pair_card_le :
    Nat.card (CommutingPairs G)≤Nat.card (CommutingPairs (AssociatedSplit N)) := by
  letI : Fintype ((G⧸N)×(G⧸N)) := Fintype.ofFinite _
  calc
    Nat.card (CommutingPairs G)=Nat.card
        (Σp:(G⧸N)×(G⧸N),Fibre (QuotientGroup.mk' N) p) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv (pairImage (QuotientGroup.mk' N)))).symm
    _=∑p:(G⧸N)×(G⧸N),Nat.card (Fibre (QuotientGroup.mk' N) p) := Nat.card_sigma
    _≤∑p:(G⧸N)×(G⧸N),Nat.card
        (Fibre (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N)) p) :=
      Finset.sum_le_sum (fun p _=>commuting_fibre_card_le N p)
    _=Nat.card (Σp:(G⧸N)×(G⧸N),
        Fibre (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N)) p) := Nat.card_sigma.symm
    _=Nat.card (CommutingPairs (AssociatedSplit N)) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv
        (pairImage (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N))))

theorem class_card_le_associated_split :
    Nat.card (ConjClasses G)≤Nat.card (ConjClasses (AssociatedSplit N)) := by
  have h := commuting_pair_card_le N
  change Nat.card {p:G×G // Commute p.1 p.2}≤
    Nat.card {p:AssociatedSplit N×AssociatedSplit N // Commute p.1 p.2} at h
  rw [card_comm_eq_card_conjClasses_mul_card,card_comm_eq_card_conjClasses_mul_card,
    associatedSplit_card N] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.card_pos (α:=G))

end SymmetricSubgroupAsymptotics.AbelianExtensionClassComparison
