import SymmetricSubgroupAsymptotics.BinaryPlaneFixedFreeInvolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementNormalPSubgroup

/-! Bind an arbitrary four-point labelling to the SAME primitive affine
profile.  Its regular elementary binary subgroup is exactly the native
linear-part kernel, and the native linear image is the actual point
complement.  In particular this image has no normal binary subgroup.
No simplicity, subgroup census, or chosen-complement identification is
assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineFourNativeLinearKernel
open BinaryPlanePermutationAffineEquiv

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X]
    (P : PrimitiveAffineProfile G X) (e : X ≃ Plane)

def permutationHom : G →* Equiv.Perm Plane :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)

def linearHom : G →* Linear := linearPart.comp (permutationHom e)

omit [Finite G] [Finite X] [Nontrivial X] in
theorem permutationHom_injective : Function.Injective (permutationHom (G := G) e) :=
  e.permCongrHom.injective.comp MulAction.toPerm_injective

omit [FaithfulSMul G X] in
theorem translation_le_kernel
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 2) : P.V ≤ (linearHom (G := G) e).ker := by
  intro g hg
  let v : P.V := ⟨g,hg⟩
  by_cases hv : v = 1
  · have hg1 : g = 1 := congrArg Subtype.val hv
    change linearHom e g = 1
    rw [hg1,map_one]
  · have hv2 : v ^ 2 = 1 := by
      apply C.equiv.injective
      apply Multiplicative.toAdd.injective
      simp only [map_pow,map_one,toAdd_pow,toAdd_one]
      rw [← hp]
      exact ZModModule.char_nsmul_eq_zero P.p _
    have hσ2 : permutationHom e g ^ 2 = 1 := by
      rw [← map_pow]
      have hg2 : g ^ 2 = 1 := congrArg Subtype.val hv2
      rw [hg2,map_one]
    have hfree : ∀ z : Plane, permutationHom e g z ≠ z := by
      intro z hz
      change e (g • e.symm z) = z at hz
      have hfix : v • e.symm z = e.symm z := by
        apply e.injective
        change e (g • e.symm z) = e (e.symm z)
        simpa only [Equiv.apply_symm_apply] using hz
      exact hv (P.eq_one_of_smul_eq (e.symm z) v hfix)
    exact BinaryPlaneFixedFreeInvolution.linearPart_eq_one _ hσ2 hfree

theorem linearHom_kernel
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 2) : (linearHom (G := G) e).ker = P.V := by
  have hle := translation_le_kernel P e hprimitive C hp
  apply le_antisymm ?_ hle
  intro g hg
  let x : X := e.symm 0
  obtain ⟨v,hv,_⟩ := P.regular x (g • x)
  have hvlin : linearPart (permutationHom e (v : G)) = 1 := hle v.property
  have hglin : linearPart (permutationHom e g) = 1 := hg
  have hzero : permutationHom e (v : G) 0 = permutationHom e g 0 := by
    change e ((v : G) • e.symm 0) = e (g • e.symm 0)
    exact congrArg e hv
  have hvg : (v : G) = g := by
    apply permutationHom_injective e
    apply affineMap_injective
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      exact hzero
    · exact hvlin.trans hglin.symm
  exact hvg ▸ v.property

def complementHom (x : X) : P.complement x →* (linearHom (G := G) e).range :=
  (linearHom e).rangeRestrict.comp (P.complement x).subtype

theorem complementHom_bijective
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 2) (x : X) : Function.Bijective (complementHom P e x) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro h hh
    have hlin : linearHom e (h : G) = 1 := congrArg Subtype.val hh
    have hV : (h : G) ∈ P.V := by
      rw [← linearHom_kernel P e hprimitive C hp]
      exact hlin
    have h1 := P.eq_one_of_smul_eq x (⟨h.val,hV⟩ : P.V) h.property
    exact Subtype.ext (congrArg (fun v : P.V => (v : G)) h1)
  · intro y
    obtain ⟨g,hg⟩ := y.property
    obtain ⟨⟨v,h⟩,hprod⟩ := (P.isComplement'_complement x).2 g
    refine ⟨h,Subtype.ext ?_⟩
    change linearHom e (h : G) = y.val
    have hvlin : linearHom e (v : G) = 1 :=
      translation_le_kernel P e hprimitive C hp v.property
    calc
      linearHom e (h : G) = linearHom e ((v : G) * (h : G)) := by
        rw [map_mul,hvlin,one_mul]
      _ = linearHom e g := congrArg (linearHom e) hprod
      _ = y.val := hg

def complementEquiv
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 2) (x : X) :
    P.complement x ≃* (linearHom (G := G) e).range :=
  MulEquiv.ofBijective (complementHom P e x)
    (complementHom_bijective P e hprimitive C hp x)

theorem normal_binary_subgroup_eq_bot
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 2) (x : X) (N : Subgroup (linearHom (G := G) e).range)
    [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  let f := complementEquiv P e hprimitive C hp x
  let M : Subgroup (P.complement x) := N.comap f.toMonoidHom
  letI : M.Normal := inferInstance
  have hM : IsPGroup P.p M := by
    rw [hp]
    exact hN.comap_of_injective f.toMonoidHom f.injective
  have hbot : M = ⊥ := P.normal_defining_p_subgroup_eq_bot hprimitive C x M hM
  apply le_antisymm ?_ bot_le
  intro y hy
  obtain ⟨z,hz⟩ := f.surjective y
  have hzM : z ∈ M := by change f z ∈ N; rwa [hz]
  rw [hbot] at hzM
  have hz1 : z = 1 := hzM
  change y = 1
  rw [← hz,hz1,map_one]

end SymmetricSubgroupAsymptotics.PrimitiveAffineFourNativeLinearKernel
