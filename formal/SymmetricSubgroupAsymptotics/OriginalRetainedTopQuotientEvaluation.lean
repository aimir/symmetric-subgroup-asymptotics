import SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv
variable {G C : Type} [Group G] [Group C]

theorem quotientSwap_mk (E N : Subgroup G) [E.Normal] [N.Normal] (x : G) :
    quotientSwap E N
      (QuotientGroup.mk' (E.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N x)) =
    QuotientGroup.mk' (N.map (QuotientGroup.mk' E)) (QuotientGroup.mk' E x) := by
  simp only [quotientSwap,MulEquiv.trans_apply,MulEquiv.symm_apply_eq] <;> rfl

theorem retainedTopEquiv_mk (E N : Subgroup G) [E.Normal] [N.Normal]
    (e : G ⧸ E ≃* C) (x : G) :
    retainedTopEquiv E N e
      (QuotientGroup.mk' (E.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N x)) =
    QuotientGroup.mk' ((N.map (QuotientGroup.mk' E)).map e.toMonoidHom)
      (e (QuotientGroup.mk' E x)) := by
  simp only [retainedTopEquiv,MulEquiv.trans_apply,quotientSwap_mk] <;> rfl

end SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv
end
