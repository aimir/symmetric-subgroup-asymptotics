import SymmetricSubgroupAsymptotics.SymmetricTopThreeEvenKernel
import SymmetricSubgroupAsymptotics.ThreeBlockOrbitRepresentatives
import SymmetricSubgroupAsymptotics.PrimeTopPermutationClassFusion
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Actual binary and ternary block fusion for full S3 top. The even
intermediate has genuine C3 top. Outside centralizers are forced into
the original full block kernel and detected on two varying fibres.
No ternary kernel is assumed abelian, and no extension is split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SymmetricTopThreeBlockClassFusion
open OriginalBlockClassBound PrimeIndexAbelianCentralizers SymmetricTopThreeEvenKernel
    SmallPermutationClassBudgets
variable {A : Type} [Group A] [MulAction A (Fin 3)]

abbrev EvenBlocks : Subgroup A := EvenTop (topMap (A:=A) (X:=Fin 3))

theorem evenBlocks_pretransitive
    (hf:Function.Surjective (topMap (A:=A) (X:=Fin 3))) :
    MulAction.IsPretransitive (EvenBlocks (A:=A)) (Fin 3) := by
  letI : MulAction.IsPretransitive (alternatingGroup (Fin 3)) (Fin 3) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 3) (by norm_num)
  constructor
  intro x y
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 3)) x y
  obtain ⟨g,hg⟩ := evenTopMap_surjective (topMap (A:=A) (X:=Fin 3)) hf a
  refine ⟨g,?_⟩
  have he := congrArg (fun t:alternatingGroup (Fin 3)=>(t:Equiv.Perm (Fin 3)) x) hg
  exact he.trans ha

theorem evenBlocks_top_card
    (hf:Function.Surjective (topMap (A:=A) (X:=Fin 3))) :
    Nat.card (Top (A:=EvenBlocks (A:=A)) (X:=Fin 3))=3 := by
  have he : Top (A:=EvenBlocks (A:=A)) (X:=Fin 3)=alternatingGroup (Fin 3) := by
    ext s
    constructor
    · rintro ⟨g,rfl⟩
      exact g.property
    · intro hs
      obtain ⟨g,hg⟩ := hf s
      refine ⟨⟨g,?_⟩,hg⟩
      change topMap (A:=A) (X:=Fin 3) g∈alternatingGroup (Fin 3)
      rw [hg]
      exact hs
  rw [he,nat_card_alternatingGroup,Nat.card_fin]
  decide

def evenFixedToBlockFixed (x:A) (hx:x∉EvenBlocks (A:=A)) :
    fixedKernel (EvenBlocks (A:=A)) x→*fixedKernel (Kernel (A:=A) (X:=Fin 3)) x where
  toFun z := ⟨⟨z.val.val,outside_commuting_even_mem_kernel
      (topMap (A:=A) (X:=Fin 3)) x hx z.val
      (Subgroup.mem_centralizer_singleton_iff.mp z.property).symm⟩,z.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem evenFixedToBlockFixed_injective (x:A) (hx:x∉EvenBlocks (A:=A)) :
    Function.Injective (evenFixedToBlockFixed x hx) := by
  intro y z he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t:fixedKernel (Kernel (A:=A) (X:=Fin 3)) x=>t.val.val) he

variable {Ω : Type} [MulAction A Ω] [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (b:Ω→Fin 3) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem outside_even_fixed_card_le (a:ℕ)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤a)
    (x:A) (hx:x∉EvenBlocks (A:=A)) :
    Nat.card (fixedKernel (EvenBlocks (A:=A)) x)≤a.factorial^2 := by
  have hxK : x∉Kernel (A:=A) (X:=Fin 3) :=
    fun hx'=>hx (kernel_le_evenTop (topMap (A:=A) (X:=Fin 3)) hx')
  exact (Nat.card_le_card_of_injective (evenFixedToBlockFixed x hx)
    (evenFixedToBlockFixed_injective x hx)).trans
      (ThreeBlockOrbitRepresentatives.outside_fixedKernel_card_le_square b hb a hsize x hxK)

include hb in
theorem full_top_class_bound
    (htop:Top (A:=A) (X:=Fin 3)=⊤) (a c:ℕ)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤a)
    (hc:∀x (L:Subgroup (Equiv.Perm (originalBlockFibre b x))),Nat.card (ConjClasses L)≤c) :
    6*Nat.card (ConjClasses A)≤c^3+8*a.factorial+9*a.factorial^2 := by
  have hf : Function.Surjective (topMap (A:=A) (X:=Fin 3)) :=
    MonoidHom.range_eq_top.mp htop
  let H := EvenBlocks (A:=A)
  letI : MulAction.IsPretransitive H (Fin 3) := evenBlocks_pretransitive hf
  have hH := PrimeTopPermutationClassFusion.prime_top_class_bound
    (A:=H) b (fun h ω=>hb h.val ω) 0 a c 3 Nat.prime_three
    (evenBlocks_top_card hf) (hsize 0) hc
  have hG := PrimeIndexUniformCentralizerClassBound.index_mul_class_card_le
    H 2 Nat.prime_two (evenTop_index (topMap (A:=A) (X:=Fin 3)) hf)
    (a.factorial^2) (outside_even_fixed_card_le b hb a hsize)
  simp only [Nat.card_fin] at hH
  omega

include hb in
theorem binary_full_top_class_card_le_ten
    (htop:Top (A:=A) (X:=Fin 3)=⊤)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤2) : Nat.card (ConjClasses A)≤10 := by
  have h := full_top_class_bound b hb htop 2 2 hsize
    (fun x L=>subgroup_class_card_le_two (hsize x) L)
  change 6*Nat.card (ConjClasses A)≤60 at h
  omega

include hb in
theorem ternary_full_top_class_card_le_sixtySix
    (htop:Top (A:=A) (X:=Fin 3)=⊤)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤3) : Nat.card (ConjClasses A)≤66 := by
  have h := full_top_class_bound b hb htop 3 3 hsize
    (fun x L=>subgroup_class_card_le_three (hsize x) L)
  change 6*Nat.card (ConjClasses A)≤399 at h
  omega

end SymmetricSubgroupAsymptotics.SymmetricTopThreeBlockClassFusion
