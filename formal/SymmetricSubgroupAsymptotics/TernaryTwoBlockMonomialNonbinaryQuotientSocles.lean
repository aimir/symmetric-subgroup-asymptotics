import SymmetricSubgroupAsymptotics.TransitiveTernaryMonomialUniform
import SymmetricSubgroupAsymptotics.TransitiveMonomialSubquotientKernel
import SymmetricSubgroupAsymptotics.CubicKernelSocleFromOrderTwoActionKernel
import SymmetricSubgroupAsymptotics.OriginalKernelSectionGeneration
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction

/-! Every nonbinary original quotient of a faithful binary monomial
TWO-coordinate cubic extension has socle bound ONE. Actual section
maps and the original normal denominator are retained throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryTwoBlockMonomialNonbinaryQuotientSocles
open OriginalKernelModuleChart
variable {G B : Type} [Group G] [Group B] [Finite G] [Finite B]
  (top : B →* Equiv.Perm (Fin 2)) (d : B → Fin 2 → ZMod 3)
  (hone : ∀ i, d 1 i=1)
  (hmul : ∀ g h i, d (g*h) i=d g i*d h (top g⁻¹ i))

abbrev blocks : B →* Equiv.Perm (Fin 2) := top
abbrev ambient := TernaryMonomialOrbitUniform.representation (blocks top) d hone hmul

/-- The exact section projection descends from G to its actual binary
acting image B. This is the cubic analogue of the original binary adapter. -/
private def sectionProjectionOnBase
    (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 3) B) (E : OriginalKernelModuleChart pi A)
    (N : Subgroup G) [N.Normal] :
    Representation.IntertwiningMap A.ρ
      ((show Representation (ZMod 3) (G ⧸ (pi.ker ⊔ N)) (E.sectionModule pi A N) from
        (E.sectionRepresentation pi A N).ρ).comp (sectionTop pi N hpi)) where
  toLinearMap := (E.sectionProjection pi A N).toLinearMap
  isIntertwining' b := by
    apply LinearMap.ext
    intro a
    obtain ⟨g,rfl⟩ := hpi b
    change E.sectionProjection pi A N (A.ρ (pi g) a)=
      (E.sectionRepresentation pi A N).ρ (sectionTop pi N hpi (pi g))
        (E.sectionProjection pi A N a)
    rw [sectionTop_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ (E.sectionProjection pi A N) g a

include hone hmul in
theorem quotientSocle (hB : IsPGroup 2 B)
    (htrans : ∀ i j : Fin 2, ∃ b : B, top b i=j)
    (hfaithful : Function.Injective (ambient top d hone hmul))
    (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 3) B) [FiniteDimensional (ZMod 3) A]
    (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (ambient top d hone hmul))
    (hj : Function.Injective j) (N : Subgroup G) [N.Normal]
    (hnonbinary : ¬ IsPGroup 2 (G ⧸ N)) : SocleNormalGeneratorBound (G ⧸ N) 1 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨n,hn⟩ := hB.exists_card_eq
  letI : NeZero (Nat.card B : ZMod 3) := ⟨by
    rw [hn,Nat.cast_pow]; exact pow_ne_zero n (by decide +kernel)⟩
  let D := G ⧸ (pi.ker ⊔ N)
  let sigma : Representation (ZMod 3) D (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ
  let f := sectionTop pi N hpi
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) y
    exact ⟨pi g,(sectionTop_apply pi N hpi g).trans hg⟩
  have hD : IsPGroup 2 D := hB.of_surjective f hf
  letI : Nontrivial (E.sectionModule pi A N) := by
    by_contra h
    letI : Subsingleton (E.sectionModule pi A N) := not_nontrivial_iff_subsingleton.mp h
    letI : Subsingleton (base pi N).ker := (E.kernelEquiv pi A N).symm.toEquiv.subsingleton
    have hinj : Function.Injective (base pi N) :=
      (base pi N).ker_eq_bot_iff.mp (base pi N).ker.eq_bot_of_subsingleton
    exact hnonbinary (hD.of_injective (base pi N) hinj)
  have hambient : UniformSubrepresentationGeneratorBound (ambient top d hone hmul) 1 :=
    TransitiveTernaryMonomialUniform.uniform_one (blocks top) d hone hmul hB 0 (htrans 0)
  have hgenA : RepresentationGeneratedBy A.ρ 1 :=
    representationGeneratedBy_of_injective_of_uniform hambient j hj
  have hgenSection : RepresentationGeneratedBy sigma 1 :=
    RepresentationGeneratedBy.of_comp sigma (QuotientGroup.mk' (pi.ker ⊔ N))
      (E.sectionGeneratedBy pi A N hpi hgenA)
  obtain ⟨m,hm⟩ := hD.exists_card_eq
  letI : NeZero (Nat.card D : ZMod 3) := ⟨by
    rw [hm,Nat.cast_pow]; exact pow_ne_zero m (by decide +kernel)⟩
  have hu := RepresentationGeneratedBy.uniform_of_invertible_order sigma hgenSection
  let q := sectionProjectionOnBase pi hpi A E N
  have hq : Function.Surjective q := E.sectionProjection_surjective pi A N
  obtain ⟨i,hi⟩ := original_equivariant_quotient_embedding A.ρ (sigma.comp f) q hq
  have hkernel : Function.Injective
      (top.comp (Representation.asGroupHom (sigma.comp f)).ker.subtype) :=
    TransitiveMonomialSubquotientKernel.kernel_top_injective
      (ambient top d hone hmul) top d (by
        intro g v r
        change d g r*v (top g⁻¹ r)=d g r*v ((top g)⁻¹ r)
        rw [map_inv])
      (TernaryMonomialOrbitUniform.coefficient_ne_zero (blocks top) d hone hmul)
      hfaithful htrans (sigma.comp f) (j.comp i) (hj.comp hi)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  letI : FiniteDimensional (ZMod 3) (E.sectionRepresentation pi A N) := by
    change FiniteDimensional (ZMod 3) (E.sectionModule pi A N)
    infer_instance
  let H := (Representation.asGroupHom (sigma.comp f)).ker
  have hcH : Nat.card H≤2 := by
    have hh := Nat.card_le_card_of_injective (top.comp H.subtype) hkernel
    simpa only [Nat.card_perm,Nat.card_fin] using hh
  have hHker : H=sigma.asGroupHom.ker.comap f := by
    ext u
    change (Representation.asGroupHom (sigma.comp f)) u=1 ↔ sigma.asGroupHom (f u)=1
    constructor
    · intro he
      have hv := congrArg Units.val he
      apply Units.ext
      change sigma (f u)=1
      change sigma (f u)=1 at hv
      exact hv
    · intro he
      have hv := congrArg Units.val he
      apply Units.ext
      change sigma (f u)=1
      change sigma (f u)=1 at hv
      exact hv
  let psi : H →* sigma.asGroupHom.ker := (f.comp H.subtype).codRestrict _ (by
    intro h
    have hle : H ≤ Subgroup.comap f sigma.asGroupHom.ker := le_of_eq hHker
    exact hle h.property)
  have hpsi : Function.Surjective psi := by
    intro b
    obtain ⟨u,hu⟩ := hf b.val
    have hm : u∈H := by
      rw [hHker]
      change sigma.asGroupHom (f u)=1
      rw [hu]
      exact b.property
    exact ⟨⟨u,hm⟩,Subtype.ext hu⟩
  have hsmall : Nat.card sigma.asGroupHom.ker≤2 :=
    (Nat.card_le_card_of_surjective psi hpsi).trans hcH
  exact CubicKernelSocleFromOrderTwoActionKernel.socle_one
    (base pi N) (base_surjective pi N) (E.sectionRepresentation pi A N)
    (E.quotientChart pi A N) hu hcop hsmall

end SymmetricSubgroupAsymptotics.TernaryTwoBlockMonomialNonbinaryQuotientSocles
