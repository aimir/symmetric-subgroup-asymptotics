import SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarUnits
import SymmetricSubgroupAsymptotics.CFSGScalarLinearOrderSelected
import SymmetricSubgroupAsymptotics.CFSGCliffordBinarySixBlockExhaustion

/-! The actual abelian-normal branch in binary dimension six. A proper
Clifford block decomposition has a checked small order budget. Otherwise
the genuine scalar-image field has degree two, three or six, and its
automorphism kernel is linear over that field on the original carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixAbelianNormal
open CFSGIsotypicCommutativeScalarField CFSGIsotypicScalarAction
  CFSGNormalAbelianScalarConjugation CFSGNormalAbelianScalarAutomorphisms
  CFSGNormalAbelianScalarKernel CFSGNormalAbelianScalarUnits

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V] [FiniteDimensional (ZMod 2) V]
  (rho : Representation (ZMod 2) G V)

theorem trace_le_fourteen_of_abelian_isotypic
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 6)
    (H : Subgroup G) [H.Normal] [IsMulCommutative H] (hH : H ≠ ⊥)
    (hiso : IsIsotypic (ZMod 2)[H] (restriction rho H).asModule)
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 14 := by
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let tau := restriction rho H
  let hss := CliffordRawRestriction.proved.semisimple rho hrho H
  letI : Finite tau.asModule :=
    Finite.of_injective tau.asModuleEquiv tau.asModuleEquiv.injective
  letI : Module.Finite (ZMod 2)[H] tau.asModule := Module.Finite.of_finite
  letI : Nontrivial tau.asModule := tau.asModuleEquiv.toEquiv.nontrivial
  letI : IsSemisimpleModule (ZMod 2)[H] tau.asModule := hss
  let K := scalarQuotient tau
  letI : Field K := scalarField tau hiso
  letI : Finite K := scalarQuotient_finite tau
  letI : Module K V := scalarModule tau
  letI : IsScalarTower (ZMod 2) K V := scalarTower tau
  letI : FiniteDimensional (ZMod 2) K := Module.Finite.of_finite
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let e := Module.finrank (ZMod 2) K
  let m := Module.finrank K V
  have hprod : e * m = 6 :=
    (scalar_dimension_product tau hss hiso).trans hd
  have hKlarge : 2 < Nat.card K := scalar_card_gt_two rho H hf hH hss hiso
  have hK : 2 ^ e = Nat.card K := FiniteField.pow_finrank_eq_natCard 2 K
  have he1 : e ≠ 1 := by
    intro he
    rw [he] at hK
    norm_num at hK
    omega
  have hdiv : e ∣ 6 := ⟨m, hprod.symm⟩
  have hcases : ∀ n ∈ Nat.divisors 6, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
    decide +kernel
  have he := hcases e (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩)
  have hem : (e = 2 ∧ m = 3) ∨ (e = 3 ∧ m = 2) ∨ (e = 6 ∧ m = 1) := by
    rcases he with he | he | he | he
    · exact False.elim (he1 he)
    · refine Or.inl ⟨he, ?_⟩
      rw [he] at hprod
      omega
    · refine Or.inr (Or.inl ⟨he, ?_⟩)
      rw [he] at hprod
      omega
    · refine Or.inr (Or.inr ⟨he, ?_⟩)
      rw [he] at hprod
      omega
  exact CFSGScalarLinearOrderSelected.trace_le_fourteen_of_scalar_kernel
    (scalarAutomorphismHom rho H) (kernelRepresentation rho H)
    (kernelRepresentation_injective rho H hf) hem T

theorem trace_le_fourteen_of_abelian_normal
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 6)
    (H : Subgroup G) [H.Normal] [IsMulCommutative H] (hH : H ≠ ⊥)
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 14 := by
  rcases CFSGCliffordBinarySixBlockExhaustion.isotypic_or_trace_le_fourteen
      rho hrho hf hd H T with hiso | hsmall
  · exact trace_le_fourteen_of_abelian_isotypic rho hrho hf hd H hH hiso T
  · exact hsmall

end SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixAbelianNormal
