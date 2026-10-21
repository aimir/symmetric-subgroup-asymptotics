import SymmetricSubgroupAsymptotics.RepresentationGeneratorSemisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite-dimensional contragredients preserve irreducibility. A simple
actual representation is uniformly cyclic. These are generic algebraic
facts, with no affine complement or finite classification premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem representation_uniform_one_of_irreducible
    (rho : Representation k G V) (hirr : Representation.IsIrreducible rho) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  letI : Representation.IsIrreducible rho := hirr
  letI : IsSimpleModule k[G] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hirr
  letI : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[G] rho.asModule
  obtain ⟨v,hv⟩ := exists_ne (0 : rho.asModule)
  have hgen : RepresentationGeneratedBy rho 1 := by
    refine ⟨fun _ => v,?_⟩
    simpa only [Set.range_const] using IsSimpleModule.span_singleton_eq_top k[G] hv
  exact RepresentationGeneratedBy.uniform_of_semisimple rho hgen

theorem representation_dual_irreducible [FiniteDimensional k V]
    (rho : Representation k G V) (hirr : Representation.IsIrreducible rho) :
    Representation.IsIrreducible rho.dual := by
  letI : Representation.IsIrreducible rho := hirr
  letI : IsSimpleModule k[G] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hirr
  letI : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V := rho.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨f,hf⟩ := exists_ne (0 : Module.Dual k V)
  have hbt : (⊥ : Subrepresentation rho.dual) ≠ ⊤ := by
    intro h
    have hm : f ∈ (⊥ : Subrepresentation rho.dual) := by rw [h]; trivial
    exact hf hm
  letI : Nontrivial (Subrepresentation rho.dual) := ⟨⟨⊥,⊤,hbt⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let N : Subrepresentation rho := {
    toSubmodule := W.toSubmodule.dualCoannihilator
    apply_mem_toSubmodule := by
      intro g v hv
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro ell hell
      have hh := hv (rho.dual g⁻¹ ell) (W.apply_mem_toSubmodule g⁻¹ hell)
      change ell (rho (g⁻¹)⁻¹ v)=0 at hh
      simpa only [inv_inv] using hh }
  have hdouble := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W.toSubmodule)
  rcases eq_bot_or_eq_top N with hn | hn
  · have ha : W.toSubmodule.dualCoannihilator=⊥ :=
      congrArg Subrepresentation.toSubmodule hn
    rw [ha,Submodule.dualAnnihilator_bot] at hdouble
    exact Or.inr (Subrepresentation.toSubmodule_injective hdouble.symm)
  · have ha : W.toSubmodule.dualCoannihilator=⊤ :=
      congrArg Subrepresentation.toSubmodule hn
    rw [ha,Submodule.dualAnnihilator_top] at hdouble
    exact Or.inl (Subrepresentation.toSubmodule_injective hdouble.symm)

theorem representation_dual_uniform_one_of_irreducible [FiniteDimensional k V]
    (rho : Representation k G V) (hirr : Representation.IsIrreducible rho) :
    UniformSubrepresentationGeneratorBound rho.dual 1 :=
  representation_uniform_one_of_irreducible rho.dual (representation_dual_irreducible rho hirr)

end SymmetricSubgroupAsymptotics
