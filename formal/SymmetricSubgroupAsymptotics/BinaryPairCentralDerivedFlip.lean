import SymmetricSubgroupAsymptotics.PGroupPermutationPointwiseAnnihilator
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! A transitive binary pair action with flip-kernel dimension greater
than one contains its literal all-pairs flip in the derived subgroup.
This supplies one selected central derived element of the actual source,
without using an original-action catalogue or a split complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance centralDerivedFlipPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem exists_central_derived_constant_flip
    (hU : IsPGroup 2 U) (i : Fin w)
    (hdim : 1 < Module.finrank (ZMod 2) F.kernelSpace) :
    ∃ z : F.top.ker,F.bits z=(fun _ => 1) ∧
      (z : U) ∈ Subgroup.center U ∧ (z : U) ∈ commutator U := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  let S := F.axisNaturalSubrepresentation (commutator U)
  have hS : S.toSubmodule ≠ ⊥ := by
    intro hbot
    have hfixed (v : F.kernelSpace) (t : F.top.range) :
        permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w) t v.val=v.val := by
      obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
      obtain ⟨k,hk⟩ := v.property
      change F.bits k.toMul=v.val at hk
      rw [←hk]
      have hc : ((k.toMul⁻¹*MulAut.conjNormal u k.toMul : F.top.ker) : U) ∈ commutator U := by
        change ⁅(k.toMul : U)⁻¹,u⁆ ∈ commutator U
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hm := (F.bits_mem_ambientAxis (commutator U)
        (k.toMul⁻¹*MulAut.conjNormal u k.toMul)).mpr hc
      rw [F.bits_commutator] at hm
      change F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k.toMul)-F.bits k.toMul ∈
        S.toSubmodule at hm
      rw [hbot] at hm
      exact sub_eq_zero.mp hm
    let j : F.kernelSpace →ₗ[ZMod 2]
        (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)).invariants := {
      toFun v := ⟨v.val,hfixed v⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    have hj : Function.Injective j := by
      intro a b he
      exact Subtype.ext (congrArg
        (fun z : (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)).invariants => z.val) he)
    have hb := j.finrank_le_finrank_of_injective hj
    rw [PermutationBinaryFourSection.invariants_finrank i] at hb
    omega
  have hone := pGroup_permutation_subrepresentation_contains_one (F.top_isPGroup hU) i S hS
  obtain ⟨z,hzD,hz⟩ := (F.mem_ambientAxis (commutator U) (fun _ => 1)).mp hone
  refine ⟨z,hz,?_,hzD⟩
  apply Subgroup.mem_center_iff.mpr
  intro u
  have he : MulAut.conjNormal u z=z := by
    apply F.bitsHom_injective
    apply Multiplicative.toAdd.injective
    change F.bits (MulAut.conjNormal u z)=F.bits z
    rw [←F.coordinateTopAction_bits,hz]
    rfl
  have hm := congrArg (fun k : F.top.ker => (k : U)*u) he
  change (u*(z : U)*u⁻¹)*u=(z : U)*u at hm
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

end SymmetricSubgroupAsymptotics.BinaryPairFrame
