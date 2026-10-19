import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerCommutators
import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction

/-! A genuine regular V4 subgroup in the ACTUAL linear centralizer of a
rank-one odd kernel. The original affine extension is never split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerKleinLift
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R regular regular_injective top)
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem cubic_centralizer : ∀ p q : Equiv.Perm (Fin 3),
    q^3=1 → q≠1 → p*q=q*p → p^3=1 := by decide +kernel

variable (C : Subgroup Frame)
  (e : oddKernel C ≃* Cubic)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)

abbrev alpha : C →* MulAut (oddKernel C) := MulAut.conjNormal
def centralRegular : Subgroup C := (alpha C).ker ⊓ regular.range.comap (top C)

def beta : centralRegular C →* regular.range :=
  ((top C).comp (centralRegular C).subtype).codRestrict _ (fun g => g.property.2)

include e heven in
theorem beta_surjective : Function.Surjective (beta C) := by
  intro r
  obtain ⟨a,ha⟩ := r.property
  obtain ⟨g,hg,hcentral⟩ :=
    BinaryPlaneAlternatingCentralizerCommutators.exists_regular_centralizing_lift C e heven a
  have halpha : alpha C g=1 := by
    apply MulEquiv.ext
    intro o
    apply Subtype.ext
    change g*(o : C)*g⁻¹=(o : C)
    rw [(hcentral o).eq,mul_assoc,mul_inv_cancel,mul_one]
  refine ⟨⟨g,halpha,?_⟩,Subtype.ext (hg.trans ha)⟩
  exact ⟨a,hg.symm⟩

include e heven in
theorem beta_kernel_cubic (x : (beta C).ker) : x^3=1 := by
  let g : C := ((x : centralRegular C) : C)
  have ht : (g : Frame).right=1 := by
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  have ha : alpha C g=1 := (x : centralRegular C).property.1
  letI : Nontrivial (oddKernel C) := e.toEquiv.nontrivial
  have hO : oddKernel C≠⊥ := (oddKernel C).nontrivial_iff_ne_bot.mp inferInstance
  have hg : g^3=1 := by
    apply Subtype.ext
    apply PermutationalWreathProduct.ext
    · funext i
      apply BinaryPlaneWreathNormalGenerators.toThree_injective
      have hpower : ((g : Frame)^3).left i=(g : Frame).left i^3 := by
        simp [pow_succ,PermutationalWreathProduct.mul_left,
          PermutationalWreathProduct.mul_right,ht]
      change BinaryPlaneWreathNormalGenerators.toThree (((g : Frame)^3).left i)=
        BinaryPlaneWreathNormalGenerators.toThree 1
      rw [hpower,map_pow,map_one]
      obtain ⟨o,ho⟩ := all_local_nontrivial C hO
        (BinaryPlaneAlternatingKernelPartition.transitive C heven) i
      apply cubic_centralizer _ (BinaryPlaneWreathNormalGenerators.toThree (localLinear C i o))
      · rw [← map_pow,local_cubic C i o,map_one]
      · intro h
        exact ho (BinaryPlaneWreathNormalGenerators.toThree_injective
          (h.trans (map_one _).symm))
      · have hc := congrArg (fun f : MulAut (oddKernel C) => (f o : C)) ha
        change g*(o : C)*g⁻¹=(o : C) at hc
        have hm : g*(o : C)=(o : C)*g := mul_inv_eq_iff_eq_mul.mp hc
        have hh := congrArg (fun z : C => (z : Frame).left i) hm
        change (((g : Frame)*((o : C) : Frame)).left i)=
          ((((o : C) : Frame)*(g : Frame)).left i) at hh
        simp only [PermutationalWreathProduct.mul_left,Pi.mul_apply,
          ht,top_one C o,inv_one,one_smul] at hh
        change (g : Frame).left i*localLinear C i o=
          localLinear C i o*(g : Frame).left i at hh
        simpa only [map_mul] using congrArg BinaryPlaneWreathNormalGenerators.toThree hh
    · change PermutationalWreathProduct.rightHom ((g : Frame)^3)=1
      rw [map_pow]
      change (g : Frame).right^3=1
      rw [ht,one_pow]
  apply Subtype.ext
  apply Subtype.ext
  exact hg

private theorem regular_binary : IsPGroup 2 regular.range := by
  have hR : IsPGroup 2 R := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  exact hR.of_surjective regular.rangeRestrict regular.rangeRestrict_surjective

include e heven in
/-- A literal homomorphic V4 lift centralizing K, chosen only in the
linear image; no section of any original affine quotient is postulated. -/
theorem exists_regular_hom : ∃ lift : R →* C, Function.Injective lift ∧
    (∀ r, top C (lift r)=regular r) ∧
    ∀ r (o : oddKernel C), Commute (lift r) (o : C) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 2 (centralRegular C) := Classical.choice inferInstance
  let b := (beta C).comp (P : Subgroup (centralRegular C)).subtype
  have hb : Function.Surjective b :=
    sylow_restrict_surjective P regular_binary (beta C) (beta_surjective C e heven)
  have hi : Function.Injective b := by
    apply b.ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    let z : (beta C).ker := ⟨(x : centralRegular C),hx⟩
    have hcube : x^3=1 := Subtype.ext
      (congrArg (fun t : (beta C).ker => (t : centralRegular C)) (beta_kernel_cubic C e heven z))
    apply Subgroup.mem_bot.mpr
    apply (P.isPGroup'.powEquiv (by decide : Nat.Coprime 2 3)).injective
    simpa only [IsPGroup.powEquiv_apply,one_pow] using hcube
  let ep : P ≃* regular.range := MulEquiv.ofBijective b ⟨hi,hb⟩
  let lift : R →* C := (centralRegular C).subtype.comp
    ((P : Subgroup (centralRegular C)).subtype.comp
      (ep.symm.toMonoidHom.comp regular.rangeRestrict))
  have htop (r : R) : top C (lift r)=regular r := by
    have hp := ep.apply_symm_apply (regular.rangeRestrict r)
    exact congrArg Subtype.val hp
  refine ⟨lift,?_,htop,?_⟩
  · intro r s h
    apply regular_injective
    exact (htop r).symm.trans ((congrArg (top C) h).trans (htop s))
  · intro r o
    have ha : alpha C (lift r)=1 := (ep.symm (regular.rangeRestrict r) : centralRegular C).property.1
    have hc := congrArg (fun f : MulAut (oddKernel C) => (f o : C)) ha
    change lift r*(o : C)*(lift r)⁻¹=(o : C) at hc
    exact mul_inv_eq_iff_eq_mul.mp hc

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerKleinLift
