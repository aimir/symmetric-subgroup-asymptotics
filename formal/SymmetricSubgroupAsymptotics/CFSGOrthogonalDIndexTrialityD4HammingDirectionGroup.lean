import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingCoherence
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum

/-! The proved coherent coordinate direction gives an ACTUAL group
homomorphism on Hamming automorphisms. For three coordinates its kernel
has index at most six. This is the local residue group, not yet an
assertion about the global original D4 geometry stabilizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {I : Type*} [DecidableEq I] {D : I → Type*} [∀ i, Nontrivial (D i)]

def hammingAut : Subgroup (Equiv.Perm (∀ i, D i)) where
  carrier := {f | ∀ x y, ClosedAdjacent (f x) (f y) ↔ ClosedAdjacent x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    have hh := hf (f.symm x) (f.symm y)
    simpa only [Equiv.apply_symm_apply] using hh.symm

def directionHom [Finite I] (base : ∀ i, D i) : hammingAut (D := D) →* Equiv.Perm I where
  toFun f := directionPermutation f.val f.property base
  map_one' := by
    apply Equiv.ext
    intro i
    have hh := image_edge_global_direction (1 : hammingAut (D := D)).val
      (1 : hammingAut (D := D)).property base (coordinateStep_edge base i)
    change DirectionEdge (directionPermutation (1 : hammingAut (D := D)).val
      (1 : hammingAut (D := D)).property base i) base (coordinateStep base i) at hh
    exact directionEdge_unique hh (coordinateStep_edge base i)
  map_mul' f g := by
    apply Equiv.ext
    intro i
    have hg := image_edge_global_direction g.val g.property base (coordinateStep_edge base i)
    have hfg := image_edge_global_direction f.val f.property base hg
    have hprod := image_edge_global_direction (f * g).val (f * g).property base
      (coordinateStep_edge base i)
    change DirectionEdge (directionPermutation (f * g).val (f * g).property base i)
      (f.val (g.val base)) (f.val (g.val (coordinateStep base i))) at hprod
    exact directionEdge_unique hprod hfg

theorem directionHom_kernel_index_le [Finite I] (base : ∀ i, D i) :
    (directionHom base).ker.index ≤ Nat.card (Equiv.Perm I) := by
  change Nat.card (hammingAut (D := D) ⧸ (directionHom base).ker) ≤ Nat.card (Equiv.Perm I)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (directionHom base)).toEquiv]
  exact Nat.card_le_card_of_injective
    (fun f : (directionHom base).range => f.val) Subtype.val_injective

theorem directionHom_kernel_index_le_six {E : Fin 3 → Type*} [∀ i, Nontrivial (E i)]
    (base : ∀ i, E i) : (directionHom base).ker.index ≤ 6 := by
  have hh := directionHom_kernel_index_le base
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
