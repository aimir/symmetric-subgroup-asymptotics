import SymmetricSubgroupAsymptotics.ChiefOrbitEvaluation
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain

/-! A constructed local elementary layer yields an actual ambient-normal
relative-head step. The lower group is its literal kernel in the original
ambient group, and the exact extendible image is enlarged only at the
last dimension comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
section Construction
variable {p : ℕ} [Fact p.Prime]
variable {A V : Type} [Group A] [Finite A] [AddCommGroup V] [Module (ZMod p) V]
variable (N H : Subgroup A) [N.Normal]
variable (ρ : Representation (ZMod p) H V) (φ : N→*Multiplicative V)
variable (he : ∀ (h:H) (n:N),(φ (MulAut.conjNormal (h:A) n)).toAdd=ρ h (φ n).toAdd)

def localChiefAmbientKernel : Subgroup A :=
  (localChiefQuotientMap H (normalChainSourceAction N) ρ φ he).ker.map N.subtype

instance localChiefAmbientKernel_normal : (localChiefAmbientKernel N H ρ φ he).Normal := by
  constructor
  intro _ hb a
  obtain ⟨n,hn,rfl⟩ := hb
  refine ⟨MulAut.conjNormal a n,?_,rfl⟩
  change localChiefQuotientMap H (normalChainSourceAction N) ρ φ he
    ((normalChainSourceAction N) a n)=1
  rw [localChiefQuotientMap_equivariant,show localChiefQuotientMap H
    (normalChainSourceAction N) ρ φ he n=1 from hn,map_one]

theorem localChiefAmbientKernel_le : localChiefAmbientKernel N H ρ φ he≤N := by
  rintro _ ⟨n,_,rfl⟩
  exact n.2

def localChiefKernelAmbientEquiv :
    (localChiefQuotientMap H (normalChainSourceAction N) ρ φ he).ker ≃*
      localChiefAmbientKernel N H ρ φ he :=
  Subgroup.equivMapOfInjective _ N.subtype Subtype.val_injective

theorem localChiefKernelAmbientEquiv_coe
    (n : (localChiefQuotientMap H (normalChainSourceAction N) ρ φ he).ker) :
    (localChiefKernelAmbientEquiv N H ρ φ he n:A)=(n.1:A) := rfl

theorem localChiefKernelAmbientEquiv_symm_coe
    (b : localChiefAmbientKernel N H ρ φ he) :
    (((localChiefKernelAmbientEquiv N H ρ φ he).symm b).1:A)=(b:A) :=
  congrArg (fun z : localChiefAmbientKernel N H ρ φ he=>(z:A))
    ((localChiefKernelAmbientEquiv N H ρ φ he).apply_symm_apply b)

def localChiefKernelRelativeMap :
    primeActionKernelCharacters p (localChiefQuotientMap H (normalChainSourceAction N) ρ φ he)
      (normalChainSourceAction N)
      (representationGroupAction (localChiefInducedImage H (normalChainSourceAction N) ρ φ he).toRepresentation)
      (localChiefQuotientMap_equivariant H (normalChainSourceAction N) ρ φ he) →ₗ[ZMod p]
        primeRelativeCharacters p (localChiefAmbientKernel N H ρ φ he) where
  toFun χ := ⟨χ.1.comp (localChiefKernelAmbientEquiv N H ρ φ he).symm.toMonoidHom.toAdditive,by
    intro a b
    let c : localChiefAmbientKernel N H ρ φ he :=
      ⟨a*(b:A)*a⁻¹,Subgroup.Normal.conj_mem inferInstance _ b.2 a⟩
    let v := (localChiefKernelAmbientEquiv N H ρ φ he).symm b
    let w : (localChiefQuotientMap H (normalChainSourceAction N) ρ φ he).ker :=
      ⟨normalChainSourceAction N a v.1,by
        change localChiefQuotientMap H (normalChainSourceAction N) ρ φ he
          (normalChainSourceAction N a v.1)=1
        rw [localChiefQuotientMap_equivariant,v.2,map_one]⟩
    have hcw : (localChiefKernelAmbientEquiv N H ρ φ he).symm c=w := by
      apply Subtype.ext
      apply Subtype.ext
      change (((localChiefKernelAmbientEquiv N H ρ φ he).symm c).1:A)=
        a*(v.1:A)*a⁻¹
      rw [localChiefKernelAmbientEquiv_symm_coe]
      change a*(b:A)*a⁻¹=a*((((localChiefKernelAmbientEquiv N H ρ φ he).symm b).1):A)*a⁻¹
      rw [localChiefKernelAmbientEquiv_symm_coe]
    change χ.1 (Additive.ofMul ((localChiefKernelAmbientEquiv N H ρ φ he).symm c))=
      χ.1 (Additive.ofMul v)
    rw [hcw]
    exact χ.2 a v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem localChiefKernelRelativeMap_injective :
    Function.Injective (localChiefKernelRelativeMap N H ρ φ he) := by
  intro χ ψ h
  apply Subtype.ext
  apply primeCharacterInflation_injective p
    (localChiefKernelAmbientEquiv N H ρ φ he).symm.toMonoidHom
    (localChiefKernelAmbientEquiv N H ρ φ he).symm.surjective
  exact congrArg Subtype.val h

theorem localChiefRetained_le_relative :
    Module.finrank (ZMod p) (localChiefRetainedCharacters H (normalChainSourceAction N) ρ φ he)≤
      Module.finrank (ZMod p) (primeRelativeCharacters p (localChiefAmbientKernel N H ρ φ he)) :=
  (Submodule.finrank_le _).trans
    ((localChiefKernelRelativeMap N H ρ φ he).finrank_le_finrank_of_injective
      (localChiefKernelRelativeMap_injective N H ρ φ he))

end Construction

theorem localChief_ternary_normal_step
    (hTracey : TraceyPrimePowerModuleInput 3)
    {A V : Type} [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (N H : Subgroup A) [N.Normal]
    (ρ : Representation (ZMod 3) H V) (φ : N→*Multiplicative V)
    (he : ∀ (h:H) (n:N),(φ (MulAut.conjNormal (h:A) n)).toAdd=ρ h (φ n).toAdd) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N):ℝ)≤
      (Module.finrank (ZMod 3) V:ℝ)*traceyTernaryEnvelope H.index+
        (Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (localChiefAmbientKernel N H ρ φ he)):ℝ) := by
  have h := localChief_ternary_step hTracey H (normalChainSourceAction N) ρ φ he
  have hr : (Module.finrank (ZMod 3)
      (localChiefRetainedCharacters H (normalChainSourceAction N) ρ φ he):ℝ)≤
      (Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (localChiefAmbientKernel N H ρ φ he)):ℝ) := by
    exact_mod_cast localChiefRetained_le_relative N H ρ φ he
  have heq := congrArg (Nat.cast : ℕ→ℝ) (normalChainSourceCharactersEquiv N 3).finrank_eq
  exact heq.symm.trans_le (h.trans (add_le_add le_rfl hr))

end SymmetricSubgroupAsymptotics
