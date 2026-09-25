import SymmetricSubgroupAsymptotics.BinaryTopNormalRegistry

/-! The exact normal-step tests can be checked in the displayed quotient
image. This avoids evaluating group words for products in the source row
group; the tested kernel remains the kernel of the same actual homomorphism. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTopKernelData

variable {G ι : Type*} [Group G] (S : BinaryTopKernelData G)

theorem liftTests_iff_hom (generators : ι → G) (x : G) :
    S.liftTests generators x ↔
      S.hom x≠1 ∧ S.hom x*S.hom x=1 ∧
        ∀ j, S.hom x*S.hom (generators j)=S.hom (generators j)*S.hom x := by
  have hfalse : S.mask x=false ↔ S.hom x≠1 := by
    change S.mask x=false ↔ ¬(S.hom x=1)
    rw [← S.mask_eq x]
    cases S.mask x <;> simp
  simp only [liftTests,hfalse,S.mask_eq,map_mul,map_div,div_eq_one]

end SymmetricSubgroupAsymptotics.BinaryTopKernelData
