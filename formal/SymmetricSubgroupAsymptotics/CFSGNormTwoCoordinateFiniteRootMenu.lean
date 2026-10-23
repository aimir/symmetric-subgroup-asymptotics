import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordOrbit
import Mathlib.SetTheory.Cardinal.Finite

/-! A finite reflection-stable menu bounds the literal integral roots.
Coverage follows from the proved root-word orbit theorem, so an emitted
menu is checked by its negative simple roots and reflection closure;
the emitter itself supplies no completeness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFiniteRootMenu
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckRootWordOrbit CFSGNormTwoCoordinatePositiveRootGenerators

def reflect {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (i:Fin r) (x:Fin r→ℤ) : Fin r→ℤ :=
  x-integerPairing A x (Pi.single i 1) • Pi.single i 1

variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
include hd hs hp ho

theorem root_mem_menu (M:Finset (Fin r→ℤ))
    (hneg:∀i:Fin r,-(Pi.single i (1:ℤ):Fin r→ℤ)∈M)
    (hclosed:∀i x,x∈M → reflect A i x∈M) (x:Roots A) : x.val∈M := by
  obtain ⟨w,j,hx⟩:=exists_word_linear_negative A hs hp b₀ s₀ x
  rw [hx]
  clear hx x
  induction w with
  | nil=>exact hneg j
  | cons i w ih=>
    exact hclosed i _ ih

theorem root_card_le (M:Finset (Fin r→ℤ))
    (hneg:∀i:Fin r,-(Pi.single i (1:ℤ):Fin r→ℤ)∈M)
    (hclosed:∀i x,x∈M → reflect A i x∈M) : Nat.card (Roots A)≤M.card := by
  let f:Roots A→M:=fun x=>⟨x.val,root_mem_menu A hd hs hp ho M hneg hclosed x⟩
  have hi:Function.Injective f:=by
    intro x y h
    have hv:=congrArg (fun z:M=>z.val) h
    exact Subtype.ext hv
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hi

theorem positive_card_le (M:Finset (Fin r→ℤ))
    (hneg:∀i:Fin r,-(Pi.single i (1:ℤ):Fin r→ℤ)∈M)
    (hclosed:∀i x,x∈M → reflect A i x∈M) :
    Nat.card (PositiveRoot A)≤(M.filter (fun x=>∀i,0≤x i)).card := by
  let P:=M.filter (fun x=>∀i,0≤x i)
  let f:PositiveRoot A→P:=fun x=>⟨x.val.val,Finset.mem_filter.mpr
    ⟨root_mem_menu A hd hs hp ho M hneg hclosed x.val,x.property⟩⟩
  have hi:Function.Injective f:=by
    intro x y h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun z:P=>z.val) h)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hi

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFiniteRootMenu
