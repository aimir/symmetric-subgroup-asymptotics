import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetCoinvariantRadicalHead
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetAugmentationMiddle

/-! An actual invariant subspace meeting the nonzero top has V4
coinvariant quotients of binary dimension at most two. Its quotient
kernel contains the entire literal radical, proved by four actual middle
augmentation words, rather than assumed through a head bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetOutsideRadicalHead
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetLoewyAugmentations
open BinaryTwistedQuartetRadicalHead (middleLinear sumLinear)

private theorem cubic_cube : ∀ u : Plane, cubic (cubic (cubic u))=u := by decide +kernel
private theorem cubic_injective : Function.Injective cubic := by
  intro u v h
  have hh := congrArg (fun w => cubic (cubic w)) h
  simpa only [cubic_cube] using hh
private theorem add_self {Q : Type} [AddCommGroup Q] [Module Bit Q] (x : Q) : x+x=0 := by
  rw [← two_smul Bit,show (2 : Bit)=0 by decide,zero_smul]
private theorem sum_flip (v : Space) : sumBlocks (flipAction v)=sumBlocks v := by
  ext i
  simp [sumBlocks,flipAction]
  abel
private theorem sum_second (v : Space) : sumBlocks (secondFlip v)=sumBlocks v := by
  ext i
  simp [sumBlocks,secondFlip]
  abel

variable (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (hflip : ∀ v, v∈W → flipAction v∈W)
    (hsecond : ∀ v, v∈W → secondFlip v∈W)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (q : W →ₗ[Bit] Q) (T : Module.End Bit Q)
    (hinter : ∀ v : W, q ⟨cycleAction v,hcycle v v.property⟩=T (q v))
    (hqflip : ∀ v : W, q ⟨flipAction v,hflip v v.property⟩=q v)
    (hqsecond : ∀ v : W, q ⟨secondFlip v,hsecond v v.property⟩=q v)

include hcycle hflip hsecond hinter hqflip hqsecond in
theorem radical_in_ambient_kernel (v : W) (hnon : sumBlocks v.val≠0) :
    ∀ w : Space, sumBlocks w=0 → w∈q.ker.map W.subtype := by
  let K := q.ker.map W.subtype
  have hkc : ∀ w, w∈K → cycleAction w∈K := by
    rintro w ⟨z,hz,rfl⟩
    refine ⟨⟨cycleAction z,hcycle z z.property⟩,?_,rfl⟩
    change q ⟨cycleAction z,hcycle z z.property⟩=0
    rw [hinter,show q z=0 from hz,map_zero]
  have hkf : ∀ w, w∈K → flipAction w∈K := by
    rintro w ⟨z,hz,rfl⟩
    refine ⟨⟨flipAction z,hflip z z.property⟩,?_,rfl⟩
    change q ⟨flipAction z,hflip z z.property⟩=0
    rw [hqflip]
    exact hz
  have hks : ∀ w, w∈K → secondFlip w∈K := by
    rintro w ⟨z,hz,rfl⟩
    refine ⟨⟨secondFlip z,hsecond z z.property⟩,?_,rfl⟩
    change q ⟨secondFlip z,hsecond z z.property⟩=0
    rw [hqsecond]
    exact hz
  let x : Space := v.val+flipAction v.val
  let y : Space := v.val+secondFlip v.val
  have hx : x∈K := by
    refine ⟨v+⟨flipAction v,hflip v v.property⟩,?_,rfl⟩
    change q (v+⟨flipAction v,hflip v v.property⟩)=0
    rw [map_add,hqflip]
    exact add_self _
  have hy : y∈K := by
    refine ⟨v+⟨secondFlip v,hsecond v v.property⟩,?_,rfl⟩
    change q (v+⟨secondFlip v,hsecond v v.property⟩)=0
    rw [map_add,hqsecond]
    exact add_self _
  have hxr : sumBlocks x=0 := by
    change sumLinear (v.val+flipAction v.val)=0
    rw [map_add]
    change sumBlocks v.val+sumBlocks (flipAction v.val)=0
    rw [sum_flip]
    exact add_self _
  have hyr : sumBlocks y=0 := by
    change sumLinear (v.val+secondFlip v.val)=0
    rw [map_add]
    change sumBlocks v.val+sumBlocks (secondFlip v.val)=0
    rw [sum_second]
    exact add_self _
  have hxm : middle x=(cubic (sumBlocks v.val),cubic (cubic (sumBlocks v.val))) :=
    BinaryTwistedQuartetAugmentationMiddle.middle_flip v.val
  have hym : middle y=(cubic (cubic (sumBlocks v.val)),cubic (sumBlocks v.val)) :=
    BinaryTwistedQuartetAugmentationMiddle.middle_second v.val
  have hxn : x≠constant (x 0) := by
    intro h
    have hh := congrArg (fun w : Space => (middle w).1) h
    change (middle x).1=(middle (constant (x 0))).1 at hh
    rw [hxm,middle_constant] at hh
    apply hnon
    apply cubic_injective
    simpa [cubic] using hh
  have hall : ∀ u : Plane, constant u∈K :=
    BinaryTwistedQuartetRadicalSubmodules.all_constants_of_nonconstant_radical
      K hkc hkf hks x hx hxr hxn
  have hxcr : sumBlocks (cycleAction x)=0 := by rw [sum_cycle,hxr]; simp [cubic]
  have hycr : sumBlocks (cycleAction y)=0 := by rw [sum_cycle,hyr]; simp [cubic]
  have hxcm : middle (cycleAction x)=
      (cubic (sumBlocks v.val),cubic (sumBlocks v.val)) := by
    rw [middle_cycle_on_radical x hxr,hxm]
    simp only [cubic_cube]
  have hycm : middle (cycleAction y)=
      (cubic (cubic (sumBlocks v.val)),sumBlocks v.val) := by
    rw [middle_cycle_on_radical y hyr,hym]
    simp only [cubic_cube]
  intro w hw
  obtain ⟨a,b,c,d,habcd⟩ := BinaryTwistedQuartetAugmentationMiddle.middle_span
    (sumBlocks v.val) (middle w).1 (middle w).2 hnon
  let z := a • x+b • y+c • cycleAction x+d • cycleAction y
  have hz : z∈K := K.add_mem
    (K.add_mem (K.add_mem (K.smul_mem a hx) (K.smul_mem b hy))
      (K.smul_mem c (hkc x hx))) (K.smul_mem d (hkc y hy))
  have hzr : sumBlocks z=0 := by
    change sumLinear (a • x+b • y+c • cycleAction x+d • cycleAction y)=0
    simp only [map_add,map_smul]
    change a • sumBlocks x+b • sumBlocks y+c • sumBlocks (cycleAction x)+
      d • sumBlocks (cycleAction y)=0
    rw [hxr,hyr,hxcr,hycr]
    simp
  have hzm : middle z=middle w := by
    change middleLinear (a • x+b • y+c • cycleAction x+d • cycleAction y)=_
    simp only [map_add,map_smul]
    change a • middle x+b • middle y+c • middle (cycleAction x)+
      d • middle (cycleAction y)=_
    rw [hxm,hym,hxcm,hycm]
    exact habcd.symm
  have hwzr : sumBlocks (w+z)=0 := by
    change sumLinear (w+z)=0
    rw [map_add]
    change sumBlocks w+sumBlocks z=0
    rw [hw,hzr,add_zero]
  have hwzm : middle (w+z)=0 := by
    change middleLinear (w+z)=0
    rw [map_add]
    change middle w+middle z=0
    rw [hzm]
    exact add_self _
  have hwz : w+z∈K := by
    rw [BinaryTwistedQuartetMiddleKernel.eq_constant (w+z) hwzr hwzm]
    exact hall _
  have he : (w+z)+z=w := by rw [add_assoc,add_self,add_zero]
  rw [← he]
  exact K.add_mem hwz hz

include hcycle hflip hsecond hinter hqflip hqsecond in
theorem rank_le_two (hq : Function.Surjective q) (v : W) (hnon : sumBlocks v.val≠0) :
    Module.finrank Bit Q≤2 := by
  let beta := sumLinear.comp W.subtype
  have hk : beta.ker≤q.ker := by
    intro w hw
    have hm := radical_in_ambient_kernel W hcycle hflip hsecond q T
      hinter hqflip hqsecond v hnon w.val hw
    obtain ⟨z,hz,he⟩ := hm
    have hzw : z=w := Subtype.ext he
    simpa only [hzw] using hz
  have hker := Submodule.finrank_mono hk
  have hb := beta.finrank_range_add_finrank_ker
  have hqrank := q.finrank_range_add_finrank_ker
  have hbr : Module.finrank Bit beta.range≤2 :=
    beta.range.finrank_le.trans (by simp [Plane])
  have hqr : q.range=⊤ := LinearMap.range_eq_top.mpr hq
  rw [hqr,finrank_top] at hqrank
  omega

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetOutsideRadicalHead
