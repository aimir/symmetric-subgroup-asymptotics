import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator

/-! An actual commuting involution for a rank-one odd kernel over regular
V4. The Sylow centralizer has faithful block action: its block kernel is
both binary and locally cubic, hence trivial. No affine splitting is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneRankOneCommutingInvolution
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open RankOneCubicSylowCentralizer (Cubic Blocks)

local instance : Fintype Blocks := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq Blocks := BinaryRegularKleinWreath.rDecidableEq

private theorem cubic_centralizer : ∀ p q : Equiv.Perm (Fin 3),
    q^3=1 → q≠1 → p*q=q*p → p^3=1 := by decide +kernel

variable (C : Subgroup (W (R := Blocks) (I := Blocks)))
  (e : oddKernel C ≃* Cubic)

def top : C →* Blocks := PermutationalWreathProduct.rightHom.comp C.subtype

include e in
/-- This proves the needed block-kernel injectivity directly in the actual
local S3 images, avoiding a separate ternary-line chart adapter. -/
theorem centralizer_block_injective
    (htrans : ∀ i j : Blocks, ∃ h : C, (h : W (R := Blocks) (I := Blocks)).right • i=j)
    (P : Sylow 2 C) :
    Function.Injective
      (((top C).comp (P : Subgroup C).subtype).comp
        (((MulAut.conjNormal : C →* MulAut (oddKernel C)).comp
          (P : Subgroup C).subtype).ker.subtype)) := by
  let a := (MulAut.conjNormal : C →* MulAut (oddKernel C)).comp
    (P : Subgroup C).subtype
  let beta := ((top C).comp (P : Subgroup C).subtype).comp a.ker.subtype
  apply beta.ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  let g : C := ((x : (P : Subgroup C)) : C)
  let k := BinaryPlaneRankOneOddGenerator.generator C e
  have ht : (g : W (R := Blocks) (I := Blocks)).right=1 := hx
  have ha : a (x : (P : Subgroup C))=1 := x.property
  have hc := congrArg (fun f : MulAut (oddKernel C) => (f k : C)) ha
  change g*(k : C)*g⁻¹=(k : C) at hc
  have hcomm : g*(k : C)=(k : C)*g := mul_inv_eq_iff_eq_mul.mp hc
  have hg3 : g^3=1 := by
    apply Subtype.ext
    apply PermutationalWreathProduct.ext
    · funext i
      apply toThree_injective
      have hpcoord : ((g : W (R := Blocks) (I := Blocks))^3).left i=
          (g : W (R := Blocks) (I := Blocks)).left i^3 := by
        simp [pow_succ,PermutationalWreathProduct.mul_left,
          PermutationalWreathProduct.mul_right,ht]
      change toThree (((g : W (R := Blocks) (I := Blocks))^3).left i)=toThree 1
      rw [hpcoord,map_pow,map_one]
      apply cubic_centralizer _ (toThree (localLinear C i k))
      · rw [← map_pow,local_cubic C i k,map_one]
      · intro h
        apply BinaryPlaneRankOneOddGenerator.local_nontrivial C e htrans i
        apply toThree_injective
        simpa only [map_one] using h
      · have he := congrArg (fun z : C => (z : W (R := Blocks) (I := Blocks)).left i) hcomm
        change (((g : W (R := Blocks) (I := Blocks))*
          ((k : C) : W (R := Blocks) (I := Blocks))).left i)=
          ((((k : C) : W (R := Blocks) (I := Blocks))*
            (g : W (R := Blocks) (I := Blocks))).left i) at he
        simp only [PermutationalWreathProduct.mul_left,Pi.mul_apply,
          ht,top_one C k,inv_one,one_smul] at he
        change (g : W (R := Blocks) (I := Blocks)).left i*localLinear C i k=
          localLinear C i k*(g : W (R := Blocks) (I := Blocks)).left i at he
        simpa only [map_mul] using congrArg toThree he
    · change PermutationalWreathProduct.rightHom
        ((g : W (R := Blocks) (I := Blocks))^3)=1
      rw [map_pow]
      change (g : W (R := Blocks) (I := Blocks)).right^3=1
      rw [ht,one_pow]
  have hp3 : (x : (P : Subgroup C))^3=1 := Subtype.ext hg3
  have hp1 : (x : (P : Subgroup C))=1 := by
    apply (P.isPGroup'.powEquiv (by decide : Nat.Coprime 2 3)).injective
    simpa only [IsPGroup.powEquiv_apply,one_pow] using hp3
  exact Subgroup.mem_bot.mpr (Subtype.ext hp1)

include e in
/-- The rank-one class itself supplies an actual involution centralizing
all of the odd kernel and moving the regular block set. -/
theorem exists_involution
    (honto : Function.Surjective (top C))
    (htrans : ∀ i j : Blocks, ∃ h : C, (h : W (R := Blocks) (I := Blocks)).right • i=j) :
    ∃ s : C, s^2=1 ∧ top C s≠1 ∧ ∀ o : oddKernel C, Commute s (o : C) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 2 C := Classical.choice inferInstance
  obtain ⟨s,_,hs,ht,hc⟩ := RankOneCubicSylowCentralizer.exists_commuting_involution
    (oddKernel C) e (top C) honto P (centralizer_block_injective C e htrans P)
  exact ⟨s,hs,ht,hc⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneRankOneCommutingInvolution
