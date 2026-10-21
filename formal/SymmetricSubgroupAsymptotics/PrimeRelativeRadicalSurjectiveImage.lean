import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! The complete relative radical commutes with an actual surjective
ambient map. Powers and mixed commutators are both mapped using the whole
source ambient; the target normal is the literal image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G H : Type*} [Group G] [Group H]

/-- No kernel-exponent or splitting assumption is needed. -/
theorem primeRelativeRadical_map_surjective
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] :
    letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
    (primeRelativeRadical p N).map f = primeRelativeRadical p (N.map f) := by
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rw [primeRelativeRadical_eq_powerCommutator,primeRelativeRadical_eq_powerCommutator]
  change (Subgroup.closure (Set.range (fun n : N => (n : G)^p)) ⊔
      ⁅N,(⊤ : Subgroup G)⁆).map f =
    Subgroup.closure (Set.range (fun n : N.map f => (n : H)^p)) ⊔
      ⁅N.map f,(⊤ : Subgroup H)⁆
  rw [Subgroup.map_sup,Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ hf,MonoidHom.map_closure]
  congr 2
  ext x
  constructor
  · rintro ⟨_,⟨n,rfl⟩,rfl⟩
    exact ⟨⟨f (n : G),⟨n,n.2,rfl⟩⟩,(map_pow f (n : G) p).symm⟩
  · rintro ⟨n,rfl⟩
    obtain ⟨g,hg,he⟩ := n.2
    refine ⟨g^p,⟨⟨g,hg⟩,rfl⟩,?_⟩
    exact (map_pow f g p).trans (congrArg (fun y => y^p) he)

end SymmetricSubgroupAsymptotics
