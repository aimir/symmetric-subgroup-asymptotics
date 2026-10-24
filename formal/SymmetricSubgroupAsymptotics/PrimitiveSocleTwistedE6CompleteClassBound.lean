import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6ClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleMinimumDegree
import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergIndex

/-! The actual fixed-field Heisenberg subgroup excludes every bounded
primitive action with a twisted-E6 component.  Proper indices transfer
through the original simple-factor equivalence and both retained socle
degree forms; no finite action catalogue is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.twistedE6_degree_ge_2048
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q) : 2048 ≤ Nat.card X := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  apply D.degree_lower_of_proper_index_lower 2048
  intro H hH
  have hm : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048
    q (H.map e.toMonoidHom) hm
  have hindex : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  exact hi.trans_eq hindex

theorem NonaffineData.subgroup_class_cube_le_of_twistedE6_allDegrees
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) :=
  D.subgroup_class_cube_le_of_twistedE6 q e
    (by have h := D.twistedE6_degree_ge_2048 q e; omega) H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
