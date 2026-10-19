import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.BinaryCubicDistinctKernelUniform
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Actual odd-kernel partition under an A4/S4 block image: zero, one
cubic line, or pairwise distinct local kernels. The distinct branch has
one actual module-generator position. No local odd kernel is inferred
merely from nonbinary status of the full block image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
abbrev Top := Equiv.Perm (Fin 4)
abbrev Cubic := Multiplicative (ZMod 3)
abbrev Frame := W (R := Top) (I := Fin 4)

private def evenPair (j : Fin 12) : Top :=
  (![1,Equiv.swap 0 1*Equiv.swap 2 3,
      Equiv.swap 0 2*Equiv.swap 1 3,Equiv.swap 0 3*Equiv.swap 1 2] : Fin 4 → Top)
    ⟨j.val%4,by omega⟩ * TernaryFourBlockPermutationGenerators.a^(j.val/4)

private theorem evenPair_even : ∀ j, evenPair j∈alternatingGroup (Fin 4) := by
  change ∀ j, Equiv.Perm.sign (evenPair j)=1
  decide +kernel

private theorem pair_cover : ∀ i j u v : Fin 4, i≠j → u≠v →
    ∃ h : Fin 12, evenPair h i=u ∧ evenPair h j=v := by decide +kernel

variable (C : Subgroup Frame)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)

def localKernel (i : Fin 4) : Subgroup (oddKernel C) := (localLinear C i).ker

include heven in
theorem pair_transports (i j u v : Fin 4) (hij : i≠j) (huv : u≠v) :
    ∃ h : C, (h : Frame).right i=u ∧ (h : Frame).right j=v := by
  obtain ⟨w,hw⟩ := pair_cover i j u v hij huv
  obtain ⟨h,hh⟩ := heven ⟨evenPair w,evenPair_even w⟩
  exact ⟨h,by rw [hh]; exact hw.1,by rw [hh]; exact hw.2⟩

include heven in
theorem transitive (i j : Fin 4) : ∃ h : C, (h : Frame).right • i=j := by
  by_cases hij : i=j
  · subst j
    exact ⟨1,rfl⟩
  · obtain ⟨h,hh,_⟩ := pair_transports C heven i j j i hij (Ne.symm hij)
    exact ⟨h,hh⟩

private theorem conjugate_mem_iff (h : C) (g : oddKernel C) (i : Fin 4) :
    (MulAut.conjNormal h : MulAut (oddKernel C)) g∈localKernel C ((h : Frame).right i) ↔
      g∈localKernel C i := by
  change localLinear C ((h : Frame).right • i)
    ((MulAut.conjNormal h : MulAut (oddKernel C)) g)=1 ↔ localLinear C i g=1
  rw [localLinear_conjugate]
  constructor
  · intro he
    have hc := congrArg (fun z => ((h : Frame).left ((h : Frame).right • i))⁻¹*z*
      (h : Frame).left ((h : Frame).right • i)) he
    simpa [mul_assoc] using hc
  · intro he
    rw [he,mul_one,mul_inv_cancel]

private theorem kernel_map (h : C) (i : Fin 4) :
    (localKernel C i).map (MulAut.conjNormal h : MulAut (oddKernel C)).toMonoidHom=
      localKernel C ((h : Frame).right i) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (conjugate_mem_iff C h x i).mpr hx
  · intro hg
    let a : MulAut (oddKernel C) := MulAut.conjNormal h
    have hx : a.symm g∈localKernel C i :=
      (conjugate_mem_iff C h (a.symm g) i).mp (by
        change a (a.symm g)∈localKernel C ((h : Frame).right i)
        rw [a.apply_symm_apply]
        exact hg)
    exact ⟨a.symm g,hx,a.apply_symm_apply g⟩

include heven in
theorem kernel_card_eq (i j : Fin 4) : Nat.card (localKernel C i)=Nat.card (localKernel C j) := by
  obtain ⟨h,hh⟩ := transitive C heven i j
  change (h : Frame).right i=j at hh
  have hm := kernel_map C h i
  rw [hh] at hm
  rw [← hm]
  exact Nat.card_congr ((MulAut.conjNormal h).subgroupMap (localKernel C i)).toEquiv

include heven in
/-- Primitivity here is proved using actual even pair transports, not a
metadata label or a presumed independent coordinate decomposition. -/
theorem partition : (∀ i, localKernel C i=localKernel C 0) ∨
    Function.Injective (localKernel C) := by
  by_cases hinj : Function.Injective (localKernel C)
  · exact Or.inr hinj
  · left
    have hex : ∃ i j, localKernel C i=localKernel C j ∧ i≠j := by
      by_contra h
      apply hinj
      intro i j he
      by_contra hn
      exact h ⟨i,j,he,hn⟩
    obtain ⟨i,j,he,hij⟩ := hex
    intro u
    by_cases hu : u=0
    · subst u; rfl
    · obtain ⟨h,hi,hj⟩ := pair_transports C heven i j u 0 hij hu
      have hm := congrArg
        (fun K : Subgroup (oddKernel C) => K.map
          (MulAut.conjNormal h : MulAut (oddKernel C)).toMonoidHom) he
      dsimp only at hm
      rw [kernel_map C h i,kernel_map C h j,hi,hj] at hm
      exact hm

/-- In the nonzero constant-kernel branch the odd layer is one actual
cubic line, proved from its joint local injection. -/
theorem rankOne_card (hO : oddKernel C≠⊥)
    (he : ∀ i, localKernel C i=localKernel C 0) : Nat.card (oddKernel C)=3 := by
  have hinj : Function.Injective (localLinear C (0 : Fin 4)) := by
    apply (localLinear C (0 : Fin 4)).ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply localLinear_joint C
    intro i
    have hi : g∈localKernel C i := (he i).symm ▸ hg
    simpa only [map_one] using hi
  let f : oddKernel C → {p : Equiv.Perm (Fin 3) // p^3=1} :=
    fun g => ⟨toThree (localLinear C 0 g),by rw [← map_pow,local_cubic,map_one]⟩
  have hf : Function.Injective f := by
    intro g h heq
    exact hinj (toThree_injective (congrArg Subtype.val heq))
  have hsmall : Nat.card (oddKernel C)≤3 := by
    have hc : Nat.card {p : Equiv.Perm (Fin 3) // p^3=1}=3 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    exact (Nat.card_le_card_of_injective f hf).trans_eq hc
  letI : Nontrivial (oddKernel C) := (oddKernel C).nontrivial_iff_ne_bot.mpr hO
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hlarge : 3≤Nat.card (oddKernel C) := by
    obtain hone | hdvd := (isPGroup_three C).card_eq_or_dvd
    · exfalso
      obtain ⟨g,hg⟩ := exists_ne (1 : oddKernel C)
      have hs : Subsingleton (oddKernel C) := (Nat.card_eq_one_iff_unique.mp hone).1
      exact hg (@Subsingleton.elim (oddKernel C) hs g 1)
    · exact Nat.le_of_dvd Nat.card_pos hdvd
  omega

def rankOneEquiv (hO : oddKernel C≠⊥)
    (he : ∀ i, localKernel C i=localKernel C 0) : oddKernel C ≃* Cubic := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact mulEquivOfPrimeCardEq (rankOne_card C hO he)
    (by rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod])

include heven in
theorem zero_rankOne_or_distinct : oddKernel C=⊥ ∨
    Nonempty (oddKernel C ≃* Cubic) ∨ Function.Injective (localKernel C) := by
  by_cases hO : oddKernel C=⊥
  · exact Or.inl hO
  · right
    rcases partition C heven with he | hd
    · exact Or.inl ⟨rankOneEquiv C hO he⟩
    · exact Or.inr hd

include heven in
/-- Actual singleton kernel classes give one packed odd-projector seed. -/
theorem distinct_uniform (hO : oddKernel C≠⊥)
    (hdistinct : Function.Injective (localKernel C)) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C) 1 := by
  let rho : Representation (ZMod 2) (oddKernel C) (Fin 4 → Plane) :=
    (BinaryPlaneCyclicWreathUniform.representation C).comp (oddKernel C).subtype
  let L : Fin 4 → oddKernel C →* Linear := localLinear C
  have happly : ∀ g v i, rho g v i=L i g (v i) := by
    intro g v i
    change localLinear C i g (v (((g : C) : Frame).right⁻¹ • i))=L i g (v i)
    rw [top_one C g,inv_one,one_smul]
  have hu := BinaryCubicDistinctKernelUniform.uniform_one rho L happly
    (isPGroup_three C) (local_cubic C)
    (all_local_nontrivial C hO (transitive C heven)) (kernel_card_eq C heven) hdistinct
  exact UniformSubrepresentationGeneratorBound.of_comp
    (BinaryPlaneCyclicWreathUniform.representation C) (oddKernel C).subtype hu

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition
