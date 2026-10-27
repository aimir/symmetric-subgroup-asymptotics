import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeGoodSylowTwentyThree
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourGoodSylowTwentyThree
import SymmetricSubgroupAsymptotics.MathieuPrimeCycleOddNormalizerWitnesses
import SymmetricSubgroupAsymptotics.PrimeCycleParityNormalizer

/-! Actual pinned M23/M24 parity reductions. Selected Sylows are the
literal cyclic subgroups of the checked product generators. No exact
source order, recovery, finite incidence capacity, or T1 premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MathieuPrimeCycleSylowChoice

/-- The action-to-permutation identity is proved with an ABSTRACT homomorphism,
so concrete matrix/permutation data never need delta reduction here. -/
theorem toPermHom_compHom_apply {G X : Type} [Group G]
    (rho : G →* Equiv.Perm X) (g : G) :
    letI : MulAction G X := MulAction.compHom X rho
    MulAction.toPermHom G X g = rho g := by
  apply Equiv.Perm.ext
  intro i
  rfl

theorem exists_sylow_eq_zpowers
    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)] (a : G)
    (hn : n=p ∨ n=p+1)
    (htype : (MulAction.toPermHom G (Fin n) a).cycleType = {p}) :
    ∃ P : Sylow p G, Nat.card P=p ∧ (P : Subgroup G)=Subgroup.zpowers a := by
  let rho := MulAction.toPermHom G (Fin n)
  have hperm : orderOf (rho a)=p := by
    change orderOf (MulAction.toPermHom G (Fin n) a)=p
    rw [←Equiv.Perm.lcm_cycleType,htype]
    simp
  have ho : orderOf a=p :=
    (orderOf_injective rho MulAction.toPerm_injective a).symm.trans hperm
  have hU : IsPGroup p (Subgroup.zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ho,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have hc : Nat.card P=p :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order P a
      (hP (Subgroup.mem_zpowers a)) ho
      (PrimeDegreeFactorialMultiplicity.source_card_prime_square_not_dvd hn)
  have he : Subgroup.zpowers a=(P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hP (by simpa only [hc,Nat.card_zpowers,ho] using (Nat.le_refl p))
  exact ⟨P,hc,he.symm⟩

end SymmetricSubgroupAsymptotics.MathieuPrimeCycleSylowChoice

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeParityOuterReduction
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M23
open CFSGMathieuTwentyThreeActualRepresentation
open CFSGMathieuTwentyThreeGoodSylowTwentyThree
open MathieuPrimeCycleOddNormalizerWitnesses

variable [Finite Model] [IsSimpleGroup Model]
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance sourceAction : MulAction Model (Fin 23) :=
  MulAction.compHom (Fin 23) permutationRepresentation
local instance sourceFaithful : FaithfulSMul Model (Fin 23) := {
  eq_of_smul_eq_smul := fun {a b} hab =>
    permutationRepresentation_injective (Equiv.Perm.ext hab) }

theorem action_product_eq :
    MulAction.toPermHom Model (Fin 23) (pinnedX*pinnedY) = m23Cycle := by
  have he : MulAction.toPermHom Model (Fin 23) (pinnedX*pinnedY) =
      permutationRepresentation (pinnedX*pinnedY) := by
    simpa only [sourceAction] using
      (MathieuPrimeCycleSylowChoice.toPermHom_compHom_apply
        permutationRepresentation (pinnedX*pinnedY))
  rw [he,map_mul]
  exact congrArg₂ (fun u v : Equiv.Perm (Fin 23) => u*v)
    permutationRepresentation_of_zero permutationRepresentation_of_one

theorem action_product_cycleType :
    (MulAction.toPermHom Model (Fin 23) (pinnedX*pinnedY)).cycleType = {23} := by
  have he : MulAction.toPermHom Model (Fin 23) (pinnedX*pinnedY) =
      permutationRepresentation (pinnedX*pinnedY) := by
    simpa only [sourceAction] using
      (MathieuPrimeCycleSylowChoice.toPermHom_compHom_apply
        permutationRepresentation (pinnedX*pinnedY))
  rw [he]
  exact pinnedProduct_cycleType

def selectedSylow : Sylow 23 Model :=
  Classical.choose (MathieuPrimeCycleSylowChoice.exists_sylow_eq_zpowers
    (pinnedX*pinnedY) (Or.inl rfl) action_product_cycleType)

theorem selectedSylow_spec :
    Nat.card selectedSylow = 23 ∧
      (selectedSylow : Subgroup Model) = Subgroup.zpowers (pinnedX*pinnedY) :=
  Classical.choose_spec (MathieuPrimeCycleSylowChoice.exists_sylow_eq_zpowers
    (pinnedX*pinnedY) (Or.inl rfl) action_product_cycleType)

theorem odd_mem_normalizer :
    m23Sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers (MulAction.toPermHom Model (Fin 23) (pinnedX*pinnedY))) :
        Set (Equiv.Perm (Fin 23))) := by
  rw [action_product_eq]
  exact m23_mem_normalizer

theorem normalizer_card (hnon : ¬IsMulCommutative Model) :
    Nat.card (Subgroup.normalizer (selectedSylow : Set Model)) = 253 := by
  exact PrimeCycleParityNormalizer.normalizer_card_eq_prime_half (q := 11)
    hnon selectedSylow selectedSylow_spec.1 (pinnedX*pinnedY) selectedSylow_spec.2
    (Or.inl rfl) action_product_cycleType (by decide)
    m23Sigma odd_mem_normalizer m23_sign

theorem prime_mul_outer_le_twice_fixed (hnon : ¬IsMulCommutative Model) :
    23 * Nat.card (Outer Model) ≤
      2 * Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms (pinnedX*pinnedY)) := by
  exact PrimeCycleParityNormalizer.prime_mul_outer_le_twice_fixed (q := 11)
    hnon selectedSylow selectedSylow_spec.1 (pinnedX*pinnedY) selectedSylow_spec.2
    (Or.inl rfl) action_product_cycleType (by decide)
    m23Sigma odd_mem_normalizer m23_sign

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeParityOuterReduction

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourParityOuterReduction
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M24
open CFSGMathieuTwentyFourActualRepresentation
open CFSGMathieuTwentyFourGoodSylowTwentyThree
open MathieuPrimeCycleOddNormalizerWitnesses

variable [Finite Model] [IsSimpleGroup Model]
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance sourceAction : MulAction Model (Fin 24) :=
  MulAction.compHom (Fin 24) permutationRepresentation
local instance sourceFaithful : FaithfulSMul Model (Fin 24) := {
  eq_of_smul_eq_smul := fun {a b} hab =>
    permutationRepresentation_injective (Equiv.Perm.ext hab) }

theorem action_product_eq :
    MulAction.toPermHom Model (Fin 24) (pinnedX*pinnedY) = m24Cycle := by
  have he : MulAction.toPermHom Model (Fin 24) (pinnedX*pinnedY) =
      permutationRepresentation (pinnedX*pinnedY) := by
    simpa only [sourceAction] using
      (MathieuPrimeCycleSylowChoice.toPermHom_compHom_apply
        permutationRepresentation (pinnedX*pinnedY))
  rw [he,map_mul]
  exact congrArg₂ (fun u v : Equiv.Perm (Fin 24) => u*v)
    permutationRepresentation_of_zero permutationRepresentation_of_one

theorem action_product_cycleType :
    (MulAction.toPermHom Model (Fin 24) (pinnedX*pinnedY)).cycleType = {23} := by
  have he : MulAction.toPermHom Model (Fin 24) (pinnedX*pinnedY) =
      permutationRepresentation (pinnedX*pinnedY) := by
    simpa only [sourceAction] using
      (MathieuPrimeCycleSylowChoice.toPermHom_compHom_apply
        permutationRepresentation (pinnedX*pinnedY))
  rw [he]
  exact pinnedProduct_cycleType

def selectedSylow : Sylow 23 Model :=
  Classical.choose (MathieuPrimeCycleSylowChoice.exists_sylow_eq_zpowers (p := 23) (n := 24)
    (pinnedX*pinnedY) (Or.inr rfl) action_product_cycleType)

theorem selectedSylow_spec :
    Nat.card selectedSylow = 23 ∧
      (selectedSylow : Subgroup Model) = Subgroup.zpowers (pinnedX*pinnedY) :=
  Classical.choose_spec (MathieuPrimeCycleSylowChoice.exists_sylow_eq_zpowers (p := 23) (n := 24)
    (pinnedX*pinnedY) (Or.inr rfl) action_product_cycleType)

theorem odd_mem_normalizer :
    m24Sigma ∈ Subgroup.normalizer
      ((Subgroup.zpowers (MulAction.toPermHom Model (Fin 24) (pinnedX*pinnedY))) :
        Set (Equiv.Perm (Fin 24))) := by
  rw [action_product_eq]
  exact m24_mem_normalizer

theorem normalizer_card (hnon : ¬IsMulCommutative Model) :
    Nat.card (Subgroup.normalizer (selectedSylow : Set Model)) = 253 := by
  exact PrimeCycleParityNormalizer.normalizer_card_eq_prime_half (p := 23) (q := 11) (n := 24)
    hnon selectedSylow selectedSylow_spec.1 (pinnedX*pinnedY) selectedSylow_spec.2
    (Or.inr rfl) action_product_cycleType (by decide)
    m24Sigma odd_mem_normalizer m24_sign

theorem prime_mul_outer_le_twice_fixed (hnon : ¬IsMulCommutative Model) :
    23 * Nat.card (Outer Model) ≤
      2 * Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms (pinnedX*pinnedY)) := by
  exact PrimeCycleParityNormalizer.prime_mul_outer_le_twice_fixed (p := 23) (q := 11) (n := 24)
    hnon selectedSylow selectedSylow_spec.1 (pinnedX*pinnedY) selectedSylow_spec.2
    (Or.inr rfl) action_product_cycleType (by decide)
    m24Sigma odd_mem_normalizer m24_sign

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourParityOuterReduction
