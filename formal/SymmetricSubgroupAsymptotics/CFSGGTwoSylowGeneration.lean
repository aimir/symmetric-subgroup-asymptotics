import SymmetricSubgroupAsymptotics.CFSGGTwoPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration

/-! Two actual conjugate Sylows generate the literal folded G2 matrix
group. The displayed positive/negative subgroups are only used as
p-subgroups and are not assumed Sylow or self-normalizing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoSylowGeneration
open CFSGGTwoSerreMatrices CFSGGTwoPositivePGroup

theorem natural_two_conjugate_sylows (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (P : Sylow p (naturalGroup K)) (g : naturalGroup K),
      Subgroup.closure ((P : Set (naturalGroup K)) ∪
        (P : Subgroup (naturalGroup K)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  letI : Fintype K := Fintype.ofFinite K
  let H := naturalGroup K
  let U := rootGroup K false
  let V := rootGroup K true
  have hjoin : U ⊔ V = H := positive_sup_negative K
  have hU : U ≤ H := by rw [← hjoin]; exact le_sup_left
  have hV : V ≤ H := by rw [← hjoin]; exact le_sup_right
  have hUp : IsPGroup p (U.subgroupOf H) :=
    (rootGroup_isPGroup K false p).of_injective
      (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom (Subgroup.subgroupOfEquivOfLe hU).injective
  have hVp : IsPGroup p (V.subgroupOf H) :=
    (rootGroup_isPGroup K true p).of_injective
      (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom (Subgroup.subgroupOfEquivOfLe hV).injective
  have htop : U.subgroupOf H ⊔ V.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hU hV, hjoin, Subgroup.subgroupOf_self]
  obtain ⟨P, g, _, hg⟩ := CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows
    (U.subgroupOf H) (V.subgroupOf H) hUp hVp htop
  exact ⟨P, g, hg⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoSylowGeneration
