import SymmetricSubgroupAsymptotics.BinaryPairLargeKernelCenter
import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection
import Mathlib.GroupTheory.Nilpotent

/-! A large actual pair kernel remains a faithful natural section after
quotienting its invariant line. Every original second-central element
acts trivially on this SAME section, hence has zero original top image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance secondCenterKernelPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))
include F

/-- Literal central kernel bits are fixed under every actual top element. -/
theorem coordinateTopAction_bits_eq_of_central (z : F.top.ker)
    (hz : (z : U)∈Subgroup.center U) (t : F.top.range) :
    F.coordinateTopAction t (F.bits z)=F.bits z := by
  obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
  rw [F.coordinateTopAction_bits]
  congr 1
  apply Subtype.ext
  change u*(z : U)*u⁻¹=(z : U)
  rw [Subgroup.mem_center_iff.mp hz u]
  simp only [mul_assoc,mul_inv_cancel,mul_one]

theorem original_second_center_le_kernel_of_large_kernel
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U) (x : Fin w)
    (hlarge : w+2<2*Module.finrank (ZMod 2) F.kernelSpace) :
    Subgroup.upperCentralSeries U 2≤F.top.ker := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  let M := F.kernelTopPermutationSubrepresentation
  let A : Submodule (ZMod 2) M.toSubmodule := M.toRepresentation.invariants
  have hstable (t : F.top.range) : A≤A.comap (M.toRepresentation t) := by
    intro v hv
    change M.toRepresentation t v∈A
    rw [hv t]
    exact hv
  let rho : Representation (ZMod 2) F.top.range (M.toSubmodule ⧸ A) := M.toRepresentation.quotient A hstable
  let q : M.toRepresentation.IntertwiningMap rho := {
    toLinearMap := A.mkQ
    isIntertwining' _ := by apply LinearMap.ext;intro v;rfl }
  have hqdim := A.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (M.toSubmodule ⧸ A)+Module.finrank (ZMod 2) A=
    Module.finrank (ZMod 2) F.kernelSpace at hqdim
  have hAdim := PermutationBinaryFourSection.subrepresentation_invariants_le_one x M
  change Module.finrank (ZMod 2) A≤1 at hAdim
  have hqLarge : Nat.card (Fin w)<2*Module.finrank (ZMod 2) (M.toSubmodule ⧸ A) := by
    simp only [Nat.card_fin]
    omega
  have hfaith : Function.Injective rho := permutationSection_injective_of_half_lt
    (F.top_isPGroup hU) x rho M q (fun a => A.mkQ_surjective a) hqLarge
  intro u hu
  have huc (v : U) : ⁅u,v⁆∈Subgroup.center U := by
    have hh := Subgroup.mem_upperCentralSeries_succ_iff.mp hu v
    simpa only [Subgroup.upperCentralSeries_one] using hh
  have hact : rho (F.top.rangeRestrict u)=1 := by
    apply LinearMap.ext
    intro a
    obtain ⟨v,rfl⟩ := A.mkQ_surjective a
    change A.mkQ (M.toRepresentation (F.top.rangeRestrict u) v)=A.mkQ v
    apply (Submodule.Quotient.eq A).mpr
    let d : M.toSubmodule := M.toRepresentation (F.top.rangeRestrict u) v-v
    obtain ⟨k,hk⟩ := F.kernelSpaceHom_bijective.2 (Multiplicative.ofAdd v)
    have hkv : (F.kernelSpaceHom k).toAdd=v := congrArg Multiplicative.toAdd hk
    have hbits : F.bits k=v.val := congrArg (fun z : F.kernelSpace => z.val) hkv
    let c : F.top.ker := k⁻¹*MulAut.conjNormal u k
    have hc : (c : U)∈Subgroup.center U := by
      have he : (c : U)=⁅u,(k : U)⁻¹⁆⁻¹ := by
        change (k : U)⁻¹*u*(k : U)*u⁻¹=⁅u,(k : U)⁻¹⁆⁻¹
        simp only [commutatorElement_def]
        group
      rw [he]
      exact (Subgroup.center U).inv_mem (huc ((k : U)⁻¹))
    have hd : d.val=F.bits c := by
      change F.coordinateTopAction (F.top.rangeRestrict u) v.val-v.val=F.bits c
      rw [←hbits]
      exact (F.bits_commutator u k).symm
    change d∈A
    intro t
    apply Subtype.ext
    change F.coordinateTopAction t d.val=d.val
    rw [hd]
    exact F.coordinateTopAction_bits_eq_of_central c hc t
  have ht : F.top.rangeRestrict u=1 := hfaith (by simpa only [map_one] using hact)
  exact congrArg Subtype.val ht
end SymmetricSubgroupAsymptotics.BinaryPairFrame
