import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFiniteRootMenu

/-! Indexed reflection certificates avoid equality searches among root
vectors. Each reflected row has an explicit retained target index;
coverage still follows from the actual root-word orbit theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIndexedRootMenu
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateFiniteRootMenu CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckRootWordOrbit
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    {I:Type} [Fintype I] (row:I→Fin r→ℤ) (negative:Fin r→I) (step:Fin r→I→I)
    (hneg:∀i,row (negative i)= -(Pi.single i (1:ℤ):Fin r→ℤ))
    (hstep:∀i j,row (step i j)=reflect A i (row j))
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
include hd hs hp ho hneg hstep

theorem root_has_index (x:Roots A) : ∃j,row j=x.val := by
  obtain ⟨w,i,hx⟩:=exists_word_linear_negative A hs hp b₀ s₀ x
  rw [hx]
  clear hx x
  induction w with
  | nil=>exact ⟨negative i,hneg i⟩
  | cons k w ih=>
    obtain ⟨j,hj⟩:=ih
    exact ⟨step k j,(hstep k j).trans (congrArg (reflect A k) hj)⟩

theorem roots_card_le : Nat.card (Roots A)≤Nat.card I := by
  let encode:Roots A→I:=fun x=>Classical.choose (root_has_index A hd hs hp ho row negative step hneg hstep x)
  have he:Function.Injective encode:=by
    intro x y h
    apply Subtype.ext
    exact (Classical.choose_spec (root_has_index A hd hs hp ho row negative step hneg hstep x)).symm.trans
      ((congrArg row h).trans (Classical.choose_spec
        (root_has_index A hd hs hp ho row negative step hneg hstep y)))
  exact Nat.card_le_card_of_injective encode he

theorem positive_roots_card_le :
    Nat.card (PositiveRoot A)≤(Finset.univ.filter (fun j=>∀i,0≤row j i)).card := by
  let encode:PositiveRoot A→{j:I //∀i,0≤row j i}:=fun x=>
    ⟨Classical.choose (root_has_index A hd hs hp ho row negative step hneg hstep x.val),by
      rw [Classical.choose_spec (root_has_index A hd hs hp ho row negative step hneg hstep x.val)]
      exact x.property⟩
  have he:Function.Injective encode:=by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have hi:=congrArg Subtype.val h
    exact (Classical.choose_spec (root_has_index A hd hs hp ho row negative step hneg hstep x.val)).symm.trans
      ((congrArg row hi).trans (Classical.choose_spec
        (root_has_index A hd hs hp ho row negative step hneg hstep y.val)))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using Nat.card_le_card_of_injective encode he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIndexedRootMenu
