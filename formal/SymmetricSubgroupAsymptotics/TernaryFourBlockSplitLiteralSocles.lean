import SymmetricSubgroupAsymptotics.SplitAffineLiteralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages

/-! A shared three-generator lift into the four-block C4-by-C2 model.
The translation seed is arbitrary: its actual generated submodule is
handled by the coprime retraction, without a spanning certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockSplitLiteralSocles

open SemidirectProduct TernaryFourBlockMetacyclicModel
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)

def lifted (reverse negate : Bool) (v : Vector) : Fin 3 → Model reverse negate :=
  ![inl (Multiplicative.ofAdd v),
    inr (inr (Multiplicative.ofAdd (1 : ZMod 2))),
    inr (inl (Multiplicative.ofAdd (1 : ZMod 4)))]

theorem complement_mem (reverse negate : Bool) (v : Vector)
    (h : Complement reverse) :
    (inr h : Model reverse negate) ∈ Subgroup.closure (Set.range (lifted reverse negate v)) := by
  let K := Subgroup.closure (Set.range (lifted reverse negate v))
  have hblock (c : Block) : (inr (inl c) : Model reverse negate) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 4)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← hc, map_pow, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))) _
  have hbit (b : Bit) : (inr (inr b) : Model reverse negate) ∈ K := by
    have hb : (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.toAdd.val = b := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← hb, map_pow, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 3))) _
  rw [← inl_left_mul_inr_right h, map_mul]
  exact K.mul_mem (hblock h.left) (hbit h.right)

def literalAction (reverse negate : Bool) : Model reverse negate →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action (blockAction reverse) (scalar reverse negate))

theorem quotientSocle (reverse negate : Bool) (v : Vector)
    (target : Fin 3 → Equiv.Perm (Fin 12)) (index : Equiv.Perm (Fin 3))
    (hbinding : ∀ i, literalAction reverse negate (lifted reverse negate v i) = target (index i))
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 2 :=
  SplitAffineLiteralSocles.quotientSocle (linearAction reverse negate)
    (literalAction reverse negate) (lifted reverse negate v) target index hbinding
    (complement_mem reverse negate v) (complement_coprime reverse) 1 2
    (representation_generated reverse negate) (complement_normalGen reverse) N

end TernaryFourBlockSplitLiteralSocles
end SymmetricSubgroupAsymptotics

end
