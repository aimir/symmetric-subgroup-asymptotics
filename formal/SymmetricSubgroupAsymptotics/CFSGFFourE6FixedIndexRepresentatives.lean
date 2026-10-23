import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormBasis
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedRootFramePilot

/-! The actual E6 diagram involution has 2+24 fixed Geck indices.
Only the pinned 24-root fixed menu is reduced in the selected norm
certificate. No enumeration of the general Roots Fintype is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedIndexRepresentatives
open CFSGIntegerMatrixPairing

def fixedCartanRepresentative : Fin 2→Fin 6 := ![1,3]

def fixedRootMenu : Finset (Fin 6→ℤ) := CFSGFFourE6FixedRootFramePilot.menu

theorem fixedCartanRepresentative_injective : Function.Injective fixedCartanRepresentative :=
  by decide +kernel

theorem fixedCartanRepresentative_fixed : ∀j:Fin 2,
    CFSG.Models.e6Twist (fixedCartanRepresentative j)=fixedCartanRepresentative j :=
  by decide +kernel

theorem fixedCartanRepresentative_cover : ∀i:Fin 6,CFSG.Models.e6Twist i=i→
    ∃j:Fin 2,i=fixedCartanRepresentative j := by decide +kernel

theorem fixedRootMenu_norm : ∀x∈fixedRootMenu,
    integerPairing CartanMatrix.E₆ x x=2 := by decide +kernel

theorem fixedRootMenu_card : fixedRootMenu.card=24 := CFSGFFourE6FixedRootFramePilot.menu_card

noncomputable section
open scoped Classical
open CFSGTwistedE6GeckDiagramCovariance CFSGFFourE6CharacteristicTwoNormImage
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateDiagramIndices CFSGSerreDiagram
open CFSGTwistedE6WeylChamber CFSGTwistedE6DiagramRootOrthogonality
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def FixedLabel := Fin 2⊕fixedRootMenu

theorem fixedLabel_card : Nat.card FixedLabel=26 := by
  change Nat.card (Fin 2⊕fixedRootMenu)=26
  rw [Nat.card_sum]
  simp only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin,Fintype.card_coe,fixedRootMenu_card]

private def fixedRoot (r:fixedRootMenu) : Roots CartanMatrix.E₆ :=
  ⟨r.val,fixedRootMenu_norm r.val r.property⟩

def fixedRepresentative : FixedLabel→GeckIndex
  | .inl i=>.inl (E6Index (fixedCartanRepresentative i))
  | .inr r=>.inr (fixedRoot r)

private theorem diagramIndex_simple (j:Fin 6) :
    diagramIndex (Sum.inl (E6Index j))=Sum.inl (E6Index (e6Permutation j)) :=
  congrArg (fun s:E6Base.support=>(Sum.inl s:GeckIndex))
    (supportPermutation_simple CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation j)

theorem fixedRepresentative_injective : Function.Injective fixedRepresentative := by
  intro a b he
  rcases a with i|r <;> rcases b with j|s
  · exact congrArg Sum.inl
      (fixedCartanRepresentative_injective (E6Index.injective (Sum.inl.inj he)))
  · change (Sum.inl (E6Index (fixedCartanRepresentative i)):GeckIndex)=Sum.inr (fixedRoot s) at he
    cases he
  · change (Sum.inr (fixedRoot r):GeckIndex)=Sum.inl (E6Index (fixedCartanRepresentative j)) at he
    cases he
  · change (Sum.inr (fixedRoot r):GeckIndex)=Sum.inr (fixedRoot s) at he
    have hroot:fixedRoot r=fixedRoot s:=Sum.inr.inj he
    exact congrArg Sum.inr (Subtype.ext (congrArg (fun t:Roots CartanMatrix.E₆=>t.val) hroot))

theorem fixedRepresentative_fixed (j:FixedLabel) :
    diagramIndex (fixedRepresentative j)=fixedRepresentative j := by
  cases j with
  | inl i=>
    change diagramIndex (Sum.inl (E6Index (fixedCartanRepresentative i)))=
      Sum.inl (E6Index (fixedCartanRepresentative i))
    rw [diagramIndex_simple]
    exact congrArg (fun k:Fin 6=>(Sum.inl (E6Index k):GeckIndex)) (fixedCartanRepresentative_fixed i)
  | inr r=>
    change (Sum.inr (diagramRoot (fixedRoot r)):GeckIndex)=Sum.inr (fixedRoot r)
    apply congrArg (fun k:Roots CartanMatrix.E₆=>(Sum.inr k:GeckIndex))
    apply Subtype.ext
    funext i
    rw [diagramRoot_coordinate]
    exact (Finset.mem_filter.mp r.property).2 i

def fixedIndexMap : FixedLabel→{x:GeckIndex // diagramIndex x=x} :=
  fun j=>⟨fixedRepresentative j,fixedRepresentative_fixed j⟩

theorem fixedIndexMap_bijective : Function.Bijective fixedIndexMap := by
  constructor
  · intro a b he
    exact fixedRepresentative_injective (congrArg Subtype.val he)
  · intro x
    rcases x with ⟨x,hx⟩
    cases x with
    | inl u=>
      obtain ⟨i,rfl⟩:=E6Index.surjective u
      rw [diagramIndex_simple] at hx
      have hi:e6Permutation i=i:=E6Index.injective (Sum.inl.inj hx)
      obtain ⟨j,hj⟩:=fixedCartanRepresentative_cover i hi
      refine ⟨Sum.inl j,Subtype.ext ?_⟩
      change (Sum.inl (E6Index (fixedCartanRepresentative j)):GeckIndex)=Sum.inl (E6Index i)
      rw [←hj]
    | inr k=>
      change (Sum.inr (diagramRoot k):GeckIndex)=Sum.inr k at hx
      have hroot:diagramRoot k=k:=Sum.inr.inj hx
      have hfixed:∀i,k.val (CFSG.Models.e6Twist i)=k.val i := by
        intro i
        have he:=congrArg (fun r:Roots CartanMatrix.E₆=>r.val i) hroot
        change (diagramRoot k).val i=k.val i at he
        rw [diagramRoot_coordinate] at he
        exact he
      have hmenu:k.val∈fixedRootMenu := Finset.mem_filter.mpr
        ⟨CFSGNormTwoCoordinateFiniteRootMenu.root_mem_menu CartanMatrix.E₆
          CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
          CartanMatrix.E₆_off_diag_nonpos CFSGE6FiniteRootMenu.menu
          CFSGE6FiniteRootMenu.negative_simple_mem CFSGE6FiniteRootMenu.reflection_closed k,hfixed⟩
      refine ⟨Sum.inr ⟨k.val,hmenu⟩,Subtype.ext ?_⟩
      rfl

def fixedIndexEquiv : FixedLabel≃{x:GeckIndex // diagramIndex x=x} :=
  Equiv.ofBijective fixedIndexMap fixedIndexMap_bijective

theorem diagramIndex_fixed_card : Nat.card {x:GeckIndex // diagramIndex x=x}=26 :=
  (Nat.card_congr fixedIndexEquiv).symm.trans fixedLabel_card

end
end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedIndexRepresentatives
