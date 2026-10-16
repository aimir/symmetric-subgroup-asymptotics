import SymmetricSubgroupAsymptotics.TransitiveSixSylowTrivialQuotient
import SymmetricSubgroupAsymptotics.BinaryPairSectionInvariantBound

/-! The exact surviving pair kernel in any binary quotient of a
transitive six-pair action has at most four elements. All sections use
the literal normal denominator of the original action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame
local instance sixPairBinaryQuotientKernelBoundPrime2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance sixPairBinaryQuotientKernelBoundPrime3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6))
    [MulAction U (Fin 6)] [MulAction.IsPretransitive U (Fin 6)]
    (hact : ∀ (u : U) (i : Fin 6), u • i = F.top u i)
    (N : Subgroup U) [N.Normal]

private theorem sylowThree_le_binary_quotient_kernel
    (hQ : IsPGroup 2 (U ⧸ N)) (P : Sylow 3 U) :
    (P : Subgroup U) ≤ N := by
  let f := QuotientGroup.mk' N
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide)
    ((P : Subgroup U).map f) (⊤ : Subgroup (U ⧸ N))
    (P.isPGroup'.map f) (hQ.to_subgroup ⊤)
  intro p hp
  apply (QuotientGroup.eq_one_iff (N := N) p).mp
  exact Subgroup.disjoint_def.mp hd (show f p ∈ (P : Subgroup U).map f from ⟨p,hp,rfl⟩)
    (Subgroup.mem_top (f p))

include hact in
/-- Odd averaging applies to this actual quotient of the correlated
kernel, rather than to an enlarged independent flip module. -/
theorem binary_quotient_kernel_section_finrank_le_two
    (hQ : IsPGroup 2 (U ⧸ N)) :
    Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) ≤ 2 := by
  let P : Sylow 3 U := Classical.choice inferInstance
  let K := F.kernelOriginalSubrepresentation hact
  let M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) P (Fin 6)) := {
    toSubmodule := F.kernelSpace
    apply_mem_toSubmodule := by
      intro p v hv
      exact K.apply_mem_toSubmodule (p : U) hv }
  let q : M.toSubmodule →ₗ[ZMod 2] (F.kernelSpace ⧸ F.normalSpace N) :=
    (F.normalSpace N).mkQ
  have htriv : ∀ (p : P) (v : M.toSubmodule), q (M.toRepresentation p v) = q v := by
    intro p v
    change (F.normalSpace N).mkQ (K.toRepresentation (p : U) v) =
      (F.normalSpace N).mkQ v
    rw [F.sectionMkQ_equivariant N hact]
    have hp : (p : U) ∈ N := sylowThree_le_binary_quotient_kernel N hQ P p.2
    have hpeq : QuotientGroup.mk' (F.top.ker ⊔ N) (p : U) = 1 :=
      (QuotientGroup.eq_one_iff (N := F.top.ker ⊔ N) (p : U)).mpr
        (Subgroup.mem_sup_right hp)
    rw [hpeq,map_one]
    rfl
  exact transitiveSix_sylowThree_trivial_quotient_finrank_le_two P M q
    (F.normalSpace N).mkQ_surjective htriv

include hact in
/-- The same literal pair-kernel section has order at most four. -/
theorem binary_quotient_kernel_section_card_le_four
    (hQ : IsPGroup 2 (U ⧸ N)) :
    Nat.card (F.kernelSpace ⧸ F.normalSpace N) ≤ 4 := by
  have hc : Nat.card (F.kernelSpace ⧸ F.normalSpace N) =
      2 ^ Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := F.kernelSpace ⧸ F.normalSpace N))
  rw [hc]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2)
    (F.binary_quotient_kernel_section_finrank_le_two hact N hQ)).trans (by decide)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
end
