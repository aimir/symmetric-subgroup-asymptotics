import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction
import Mathlib.Algebra.CharP.CharAndCard

/-! Transfer the proved binary elementary pair through the actual central
quotient and the checked original Serre-model equivalence. Rank starts at
three, so the excluded original C2(2) parameter never enters this theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryModelGeneration
open CFSGSymplecticSerreMatrices CFSGSymplecticBinaryGeneration
variable {K : Type} [Field K] [CharP K 2]

theorem projective_exists_generating_pair (hcard : Nat.card K=2) (s : ℕ) :
    ∃x y : elementaryProjective K (s+3),
      Subgroup.closure ({x,y} : Set (elementaryProjective K (s+3)))=⊤ := by
  obtain ⟨x,y,hxy⟩ := elementary_exists_generating_pair hcard s
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s+3)))
  refine ⟨pi x,pi y,?_⟩
  have he := congrArg (Subgroup.map pi) hxy
  simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective _)] using he

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryModelGeneration

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSGSymplecticSerreMatrices CFSGSymplecticBinaryModelGeneration

theorem typeC_binary_twoGenerated (s : ℕ) (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.C (s+3) q)] : TwoGenerated (CFSG.Models.C (s+3) q) := by
  letI : Fintype q.Field := Fintype.ofFinite q.Field
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card q.Field=2 := q.card_field.trans hq
  letI : CharP q.Field 2 := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨x,y,hxy⟩ := projective_exists_generating_pair (K:=q.Field) hcard s
  let e := serreProjectiveEquivElementaryProjective q.Field (s+2)
  refine ⟨{e.symm x,e.symm y},?_,Finset.card_le_two⟩
  have he := congrArg (Subgroup.map e.symm.toMonoidHom) hxy
  simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    Finset.coe_insert,Finset.coe_singleton] using he

end SymmetricSubgroupAsymptotics.CFSGReduction
