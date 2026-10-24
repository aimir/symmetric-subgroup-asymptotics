import SymmetricSubgroupAsymptotics.IrreducibleLinearNormalPSubgroup
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-! The actual point complement of a primitive affine profile has no
nontrivial normal subgroup of defining-prime order. Its faithful
irreducible representation is the already constructed conjugation
action on the SAME elementary translation chart. No simple-factor
classification or generator budget is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem normal_defining_p_subgroup_eq_bot
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (x : X) (N : Subgroup (P.complement x)) [N.Normal] (hN : IsPGroup P.p N) : N = ⊥ := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    (C.equiv.symm.injective.comp Multiplicative.ofAdd.injective)
  let rho := (P.complementRepresentation hprimitive C x).ρ
  letI : Representation.IsIrreducible rho := P.complementRepresentation_irreducible hprimitive C x
  have hirr : ∀ W : Submodule (ZMod P.p) C.V,
      (∀ (h : P.complement x) (v : C.V), v ∈ W → rho h v ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let U : Subrepresentation rho := ⟨W,fun h v hv => hW h v hv⟩
    rcases eq_bot_or_eq_top U with hbot | htop
    · exact Or.inl (congrArg Subrepresentation.toSubmodule hbot)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule htop)
  exact IrreducibleLinearNormalPSubgroup.normal_p_subgroup_eq_bot rho hirr
    (P.complementRepresentation_injective hprimitive C x) N hN

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
