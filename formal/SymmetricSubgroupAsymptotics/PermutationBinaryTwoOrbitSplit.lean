import SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitFiltration
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex

/-! The whole original action removes the possible extension graph.

The filtration identifies only one full orbit image and one kernel
image. An element of the original transitive group translates one
normal-subgroup orbit onto the other. Stability under that same element
forces both original coordinate sums to vanish. The resulting inclusion
is an equality by the exact six-dimensional filtration count.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Pointwise
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

variable {G X : Type} [Group G] [MulAction G X] [Finite X]
    (H : Subgroup G)

/-- Sum on a literal original H-orbit. -/
def orbitSum (o : MulAction.orbitRel.Quotient H X) : (X → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ x : o.orbit,f x.val
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' _ _ := by simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]

/-- Functions whose sum vanishes on each of two actual orbit subsets. -/
def twoOrbitAugmentation (o₁ o₂ : MulAction.orbitRel.Quotient H X) :
    Submodule (ZMod 2) (X → ZMod 2) :=
  ((orbitSum H o₁).prod (orbitSum H o₂)).ker

theorem orbitSum_single_mem (o : MulAction.orbitRel.Quotient H X)
    (x : o.orbit) (c : ZMod 2) : orbitSum H o (Pi.single x.val c)=c := by
  have he : (fun y : o.orbit => (Pi.single x.val c : X → ZMod 2) y.val)=Pi.single x c := by
    funext y
    by_cases hy : y=x
    · subst y
      simp
    · have hv : y.val≠x.val := fun h => hy (Subtype.ext h)
      simp [hy,hv]
  change (∑ y : o.orbit,(Pi.single x.val c : X → ZMod 2) y.val)=c
  rw [he]
  simp

theorem orbitSum_single_not_mem (o : MulAction.orbitRel.Quotient H X)
    (x : X) (hx : x∉o.orbit) (c : ZMod 2) : orbitSum H o (Pi.single x c)=0 := by
  change (∑ y : o.orbit,(Pi.single x c : X → ZMod 2) y.val)=0
  apply Finset.sum_eq_zero
  intro y _
  have hy : y.val≠x := by intro he; exact hx (he ▸ y.property)
  simp [hy]

theorem jointSum_surjective (o₁ o₂ : MulAction.orbitRel.Quotient H X) (hne : o₁≠o₂) :
    Function.Surjective ((orbitSum H o₁).prod (orbitSum H o₂)) := by
  let x₁ : o₁.orbit := ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  let x₂ : o₂.orbit := ⟨o₂.nonempty_orbit.choose,o₂.nonempty_orbit.choose_spec⟩
  have hx₁ : x₁.val∉o₂.orbit := by
    intro hm
    exact hne ((MulAction.orbitRel.Quotient.mem_orbit.mp x₁.property).symm.trans
      (MulAction.orbitRel.Quotient.mem_orbit.mp hm))
  have hx₂ : x₂.val∉o₁.orbit := by
    intro hm
    exact hne ((MulAction.orbitRel.Quotient.mem_orbit.mp hm).symm.trans
      (MulAction.orbitRel.Quotient.mem_orbit.mp x₂.property))
  intro p
  refine ⟨Pi.single x₁.val p.1+Pi.single x₂.val p.2,?_⟩
  apply Prod.ext
  · change orbitSum H o₁ (Pi.single x₁.val p.1+Pi.single x₂.val p.2)=p.1
    rw [map_add,orbitSum_single_mem,orbitSum_single_not_mem H o₁ x₂.val hx₂,add_zero]
  · change orbitSum H o₂ (Pi.single x₁.val p.1+Pi.single x₂.val p.2)=p.2
    rw [map_add,orbitSum_single_not_mem H o₂ x₁.val hx₁,orbitSum_single_mem,zero_add]

theorem twoOrbitAugmentation_finrank (o₁ o₂ : MulAction.orbitRel.Quotient H X)
    (hne : o₁≠o₂) (hX : Nat.card X=8) :
    Module.finrank (ZMod 2) (twoOrbitAugmentation H o₁ o₂)=6 := by
  have hd := ((orbitSum H o₁).prod (orbitSum H o₂)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (jointSum_surjective H o₁ o₂ hne),finrank_top,
    Module.finrank_prod,Module.finrank_self,
    Module.finrank_pi,Fintype.card_eq_nat_card,hX] at hd
  change 1+1+Module.finrank (ZMod 2) (twoOrbitAugmentation H o₁ o₂)=8 at hd
  omega

variable [H.Normal]

/-- A literal original group element, acting on the original point sets. -/
def orbitTranslation (o₁ o₂ : MulAction.orbitRel.Quotient H X)
    (g : G) (hg : g • o₁.orbit=o₂.orbit) : o₁.orbit ≃ o₂.orbit where
  toFun x := ⟨g • x.val,by
    have hx : g • x.val∈g • o₁.orbit := Set.smul_mem_smul_set x.property
    rw [hg] at hx
    exact hx⟩
  invFun x := ⟨g⁻¹ • x.val,by
    have hback : g⁻¹ • o₂.orbit=o₁.orbit := by
      rw [← hg,← mul_smul,inv_mul_cancel,one_smul]
    have hx : g⁻¹ • x.val∈g⁻¹ • o₂.orbit := Set.smul_mem_smul_set x.property
    rw [hback] at hx
    exact hx⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

theorem orbitSum_translate (o₁ o₂ : MulAction.orbitRel.Quotient H X)
    (g : G) (hg : g • o₁.orbit=o₂.orbit) (f : X → ZMod 2) :
    orbitSum H o₁ f=orbitSum H o₂ (permutationFunctionRepresentation (ZMod 2) G X g f) := by
  have he := Equiv.sum_comp (orbitTranslation H o₁ o₂ g hg)
    (fun z : o₂.orbit => permutationFunctionRepresentation (ZMod 2) G X g f z.val)
  change (∑ y : o₁.orbit,f (g⁻¹ • (g • y.val)))=
    ∑ z : o₂.orbit,f (g⁻¹ • z.val) at he
  simpa only [inv_smul_smul] using he

variable [MulAction.IsPretransitive G X]

theorem exists_orbit_translation (o₁ o₂ : MulAction.orbitRel.Quotient H X) :
    ∃ g : G,g • o₁.orbit=o₂.orbit := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G o₁.out o₂.out
  refine ⟨g,?_⟩
  rw [o₁.orbit_eq_orbit_out Quotient.out_eq',o₂.orbit_eq_orbit_out Quotient.out_eq',
    MulAction.smul_orbit_eq_orbit_smul,hg]

variable (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))

/-- Restriction of the actual original module, retaining its full
correlated underlying subspace. -/
def restrictedModule : Subrepresentation (permutationFunctionRepresentation (ZMod 2) H X) where
  toSubmodule := M.toSubmodule
  apply_mem_toSubmodule h _ hm := M.apply_mem_toSubmodule (h:G) hm

/-- The whole original action supplies the missing coordinate equality.
This is the step that excludes an extension graph outside the first
augmentation hyperplane. -/
theorem module_le_twoOrbitAugmentation_of_secondImage
    (o₁ o₂ : MulAction.orbitRel.Quotient H X)
    (hsecond : (PermutationBinaryTwoOrbitFiltration.secondImage
      (restrictedModule H M) o₂).toSubmodule=PermutationAugmentation.space (ZMod 2) o₂.orbit) :
    M.toSubmodule≤twoOrbitAugmentation H o₁ o₂ := by
  have hsum₂ : ∀ f∈M.toSubmodule,orbitSum H o₂ f=0 := by
    intro f hf
    have hm : permutationSubrepresentationOrbitRestriction (restrictedModule H M) o₂
        ⟨f,hf⟩∈(PermutationBinaryTwoOrbitFiltration.secondImage
          (restrictedModule H M) o₂).toSubmodule := ⟨⟨f,hf⟩,rfl⟩
    rw [hsecond] at hm
    have huniv : @Finset.univ o₂.orbit (Fintype.ofFinite o₂.orbit) =
        @Finset.univ o₂.orbit (Subtype.fintype (Membership.mem o₂.orbit)) := by
      ext x
      simp only [Finset.mem_univ]
    simpa only [PermutationAugmentation.space,LinearMap.mem_ker,
      PermutationAugmentation.coordinateSum,permutationSubrepresentationOrbitRestriction,
      orbitSum,Representation.IntertwiningMap.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
      huniv] using hm
  obtain ⟨g,hg⟩ := exists_orbit_translation H o₁ o₂
  intro f hf
  change (orbitSum H o₁ f,orbitSum H o₂ f)=(0,0)
  apply Prod.ext
  · rw [orbitSum_translate H o₁ o₂ g hg]
    exact hsum₂ _ (M.apply_mem_toSubmodule g hf)
  · exact hsum₂ f hf

variable [Finite G]

/-- The exact original module is the sum-zero module on the two actual
normal-subgroup orbits. No module-splitting premise is supplied. -/
theorem exists_module_eq_twoOrbitAugmentation
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (hH : IsPGroup 2 H) (hX : Nat.card X=8)
    (hclasses : Nat.card (MulAction.orbitRel.Quotient H X)=2)
    (hcard : ∀ o : MulAction.orbitRel.Quotient H X,Nat.card o.orbit=4)
    (q : M.toSubmodule →ₗ[ZMod 2] A) (hq : Function.Surjective q)
    (htrivial : ∀ (h : H) (m : M.toSubmodule),q (M.toRepresentation (h:G) m)=q m)
    (hA : 4≤Module.finrank (ZMod 2) A) :
    ∃ o₁ o₂ : MulAction.orbitRel.Quotient H X,
      o₁≠o₂ ∧ (∀ o : MulAction.orbitRel.Quotient H X,o=o₁ ∨ o=o₂) ∧
      M.toSubmodule=twoOrbitAugmentation H o₁ o₂ ∧
      Module.finrank (ZMod 2) M.toSubmodule=6 := by
  obtain ⟨o₁,o₂,hne,hcover,_,hsecond,hdim⟩ :=
    PermutationBinaryTwoOrbitFiltration.exists_filtration_eq_augmentation
      (restrictedModule H M) hH hclasses hcard q hq htrivial hA
  have hle := module_le_twoOrbitAugmentation_of_secondImage H M o₁ o₂ hsecond
  have htarget := twoOrbitAugmentation_finrank H o₁ o₂ hne hX
  refine ⟨o₁,o₂,hne,hcover,?_,hdim⟩
  apply Submodule.eq_of_le_of_finrank_le hle
  change Module.finrank (ZMod 2) (twoOrbitAugmentation H o₁ o₂)≤
    Module.finrank (ZMod 2) (restrictedModule H M).toSubmodule
  omega

end SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

namespace SymmetricSubgroupAsymptotics

variable {G X A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The common-character residual determines the original permutation
preimage exactly. Its original lower quotient kernel is not replaced by
any coordinate product or by the whole normal subgroup of a larger group. -/
theorem permutationBinary_twoBlockCharacter_original_module_eq
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hA : Module.finrank (ZMod 2) A=4)
    (data : RepresentationBinaryCommonCharacter.TwoBlockCharacter ρ) :
    ∃ o₁ o₂ : MulAction.orbitRel.Quotient ρ.ker X,
      o₁≠o₂ ∧ (∀ o : MulAction.orbitRel.Quotient ρ.ker X,o=o₁ ∨ o=o₂) ∧
      M.toSubmodule=PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation ρ.ker o₁ o₂ ∧
      Module.finrank (ZMod 2) M.toSubmodule=6 := by
  obtain ⟨hclasses,hcard⟩ := permutationBinary_twoBlockCharacter_orbits hG x hX ρ M q hq hA data
  apply PermutationBinaryTwoOrbitSplit.exists_module_eq_twoOrbitAugmentation ρ.ker M
    (hG.to_subgroup ρ.ker) hX hclasses hcard q.toLinearMap hq ?_ hA.ge
  intro g m
  change q (M.toRepresentation (g:G) m)=q m
  rw [Representation.IntertwiningMap.isIntertwining _ _ q]
  have hg : ρ (g:G)=1 := g.property
  rw [hg]
  rfl

end SymmetricSubgroupAsymptotics
