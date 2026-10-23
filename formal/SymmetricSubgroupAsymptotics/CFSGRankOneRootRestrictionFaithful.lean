import SymmetricSubgroupAsymptotics.CFSGRankOnePairAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness

/-! An ordered opposite Sylow-pair stabilizer restricts faithfully to
one root group when that root group is transitive on all the other Sylows.
Faithfulness uses the SAME simple group's inner action, not a lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRankOneRootRestrictionFaithful
variable {G : Type*} [Group G] {p : ℕ}

theorem automorphism_conjugation_smul (f : MulAut G) (g : G) (P : Sylow p G) :
    f • (g • P)=(f g) • (f • P) := by
  apply Sylow.ext
  change ((P:Subgroup G).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
    ((P:Subgroup G).map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change f (g*x*g⁻¹)=f g*f x*(f g)⁻¹
  simp only [map_mul,map_inv]

theorem eq_one_of_fixed_root_and_opposite [IsSimpleGroup G]
    (P : Sylow p G) (w : G) (hw : w • P≠P)
    (htrans : ∀Q : Sylow p G,Q≠P → ∃u : P,(u:G) • (w • P)=Q)
    (f : MulAut G) (hfP : f • P=P) (hfO : f • (w • P)=w • P)
    (hfix : ∀u : P,f (u:G)=(u:G)) : f=1 := by
  let pi := MulAction.toPermHom (MulAut G) (Sylow p G)
  have hinj : Function.Injective pi :=
    CFSGInnerActionFaithfulness.injective_of_inner_nontrivial pi ⟨w,by
      intro he
      have h := congrArg (fun e : Equiv.Perm (Sylow p G) => e P) he
      exact hw h⟩
  apply hinj
  rw [map_one]
  apply Equiv.ext
  intro Q
  change f • Q=Q
  by_cases hQ : Q=P
  · simpa only [hQ] using hfP
  · obtain ⟨u,hu⟩ := htrans Q hQ
    rw [←hu,automorphism_conjugation_smul,hfix,hfO]

end SymmetricSubgroupAsymptotics.CFSGRankOneRootRestrictionFaithful
