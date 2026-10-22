import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalRealization
import Mathlib.Data.Fintype.EquivFin

/-! Genuine paired fixed-root words in the ORIGINAL twisted-A source.
The commutation is proved on the original integral lattice, not pulled
back from a natural-image calculation. Adjacent reversed nodes (notably
rank two) are deliberately outside this orthogonal-node construction. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration

theorem extension_two_card (q : CFSG.PrimePower) :
    Nat.card (q.Extension 2) = q.order ^ 2 := by
  change Nat.card (GaloisField q.prime (2 * q.exponent)) = (q.prime ^ q.exponent) ^ 2
  rw [GaloisField.card q.prime (2 * q.exponent) (by have := q.exponent_pos; omega), ← pow_mul]
  rw [Nat.mul_comm 2 q.exponent]

theorem extension_two_pow_twice (q : CFSG.PrimePower) (t : q.Extension 2) :
    (t ^ q.order) ^ q.order = t := by
  letI : Fintype (q.Extension 2) := Fintype.ofFinite _
  calc
    _ = t ^ (q.order ^ 2) := by rw [pow_two, pow_mul]
    _ = t ^ Nat.card (q.Extension 2) := by rw [extension_two_card]
    _ = t := by simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card t

theorem paired_root_mem_fixed (r : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin r) (hi : CartanMatrix.A r i i.rev = 0) (t : q.Extension 2) :
    ((modelRoot (CartanMatrix.A r) (q.Extension 2) neg i t) *
      (modelRoot (CartanMatrix.A r) (q.Extension 2) neg i.rev (t ^ q.order))).val ∈
        fixedSubgroup (CartanMatrix.A r) (q.Extension 2)
          CFSG.Models.reverseNode (fun _ => q.order) := by
  let u := modelRoot (CartanMatrix.A r) (q.Extension 2) neg i t
  let v := modelRoot (CartanMatrix.A r) (q.Extension 2) neg i.rev (t ^ q.order)
  have huv : (u.val, v.val) ∈ twistGraph (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) :=
    Subgroup.subset_closure ⟨neg, i, t, rfl, rfl⟩
  have hvu : (v.val, u.val) ∈ twistGraph (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) := by
    apply Subgroup.subset_closure
    refine ⟨neg, i.rev, t ^ q.order, rfl, ?_⟩
    change IsRootElement (CartanMatrix.A r) (q.Extension 2) neg i.rev.rev
      ((t ^ q.order) ^ q.order) u.val
    rw [Fin.rev_rev, extension_two_pow_twice]
    rfl
  have hc : u.val * v.val = v.val * u.val :=
    congrArg (fun g : Model (CartanMatrix.A r) (q.Extension 2) => g.val)
      (CFSGSerreCrossNodeCommutation.modelRoots_commute_of_cartan_zero
        (CartanMatrix.A r) (q.Extension 2) neg i i.rev hi t (t ^ q.order)).eq
  refine ⟨(u * v).property, ?_⟩
  have hm := (twistGraph (CartanMatrix.A r) (q.Extension 2)
    CFSG.Models.reverseNode (fun _ => q.order)).mul_mem huv hvu
  change (u.val * v.val, v.val * u.val) ∈ _ at hm
  change (u.val * v.val, u.val * v.val) ∈
    twistGraph (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
  rwa [← hc] at hm

def pairedFixedRoot (r : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin r) (hi : CartanMatrix.A r i i.rev = 0) (t : q.Extension 2) :
    fixedSubgroup (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) :=
  ⟨((modelRoot (CartanMatrix.A r) (q.Extension 2) neg i t) *
      (modelRoot (CartanMatrix.A r) (q.Extension 2) neg i.rev (t ^ q.order))).val,
    paired_root_mem_fixed r q neg i hi t⟩

theorem pairedFixedRoot_toModel (r : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin r) (hi : CartanMatrix.A r i i.rev = 0) (t : q.Extension 2) :
    CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) (pairedFixedRoot r q neg i hi t) =
        modelRoot (CartanMatrix.A r) (q.Extension 2) neg i t *
          modelRoot (CartanMatrix.A r) (q.Extension 2) neg i.rev (t ^ q.order) := rfl

theorem pairedFixedRoot_natural_action (r : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin r) (hi : CartanMatrix.A r i i.rev = 0) (t : q.Extension 2) :
    twistedFixedAction r q (pairedFixedRoot r q neg i hi t) =
      naturalElementaryAction (q.Extension 2) r
        (CFSGSerreSquareZeroMatrix.elementaryRoot (q.Extension 2)
          (naturalRootUnit (q.Extension 2) r) neg i t *
        CFSGSerreSquareZeroMatrix.elementaryRoot (q.Extension 2)
          (naturalRootUnit (q.Extension 2) r) neg i.rev (t ^ q.order)) := by
  change naturalAction (q.Extension 2) r
    (CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) (pairedFixedRoot r q neg i hi t)) = _
  rw [pairedFixedRoot_toModel, map_mul, map_mul]
  exact congrArg₂ (fun a b => a * b)
    (CFSGSerreSquareZeroMatrix.source_root_action_eq_elementary (realizationData r)
      (q.Extension 2) (naturalRootUnit (q.Extension 2) r)
      (naturalRootUnit_val (q.Extension 2) r) (naturalRootUnit_inv_val (q.Extension 2) r)
      neg i t)
    (CFSGSerreSquareZeroMatrix.source_root_action_eq_elementary (realizationData r)
      (q.Extension 2) (naturalRootUnit (q.Extension 2) r)
      (naturalRootUnit_val (q.Extension 2) r) (naturalRootUnit_inv_val (q.Extension 2) r)
      neg i.rev (t ^ q.order))

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
