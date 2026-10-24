import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalAutomorphism
import SymmetricSubgroupAsymptotics.CFSGSerreModelHomGraph

/-! Functionality of the literal ORIGINAL ReeF4 twist graph, including
the Tits defining field. The constructed homomorphism acts on the
original Model itself; no lift to ambient linear automorphisms or
fixed points of a quotient is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGraph
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGSerreModelHomGraph
local notation "A"=>CartanMatrix.F₄

theorem original_twistGraph_eq_range (m:ℕ):
    twistGraph A (Field m) CFSG.Models.reverseNode (originalExponent m)=
      (graphHom A (Field m) (reeAutomorphism m).toMonoidHom).range:=
  twistGraph_eq_range A (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m)

theorem original_graph_model_iff (m:ℕ) (g h:Model A (Field m)):
    (g.val,h.val)∈twistGraph A (Field m) CFSG.Models.reverseNode (originalExponent m)↔
      reeAutomorphism m g=h:=
  mem_twistGraph_model_iff A (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m) g h

theorem original_fixed_model_iff (m:ℕ) (g:Model A (Field m)):
    g.val∈fixedSubgroup A (Field m) CFSG.Models.reverseNode (originalExponent m)↔
      reeAutomorphism m g=g:=
  mem_fixedSubgroup_model_iff A (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m) g

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGraph
