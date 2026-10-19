import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.RegularKleinKernelClassColoring
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Actual kernel-class geometry of the correlated cubic layer over V4.
Conjugation transports projection kernels; constant kernel partition forces
one cubic line, otherwise four-point geometry supplies the two colors. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneKleinKernelGeometry
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
abbrev R := BinaryRegularKleinWreath.R
abbrev Cubic := Multiplicative (ZMod 3)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

variable (C : Subgroup (W (R := R) (I := R)))
def localKernel (i : R) : Subgroup (oddKernel C) := (localLinear C i).ker

theorem conjugate_mem_iff (h : C) (g : oddKernel C) (i : R) :
    (MulAut.conjNormal h : MulAut (oddKernel C)) g∈localKernel C ((h : W (R := R) (I := R)).right*i) ↔
      g∈localKernel C i := by
  change localLinear C ((h : W (R := R) (I := R)).right*i)
    ((MulAut.conjNormal h : MulAut (oddKernel C)) g)=1 ↔ localLinear C i g=1
  have hc := localLinear_conjugate C h g i
  change localLinear C ((h : W (R := R) (I := R)).right*i)
    ((MulAut.conjNormal h : MulAut (oddKernel C)) g)=
      (h : W (R := R) (I := R)).left ((h : W (R := R) (I := R)).right*i)*
        localLinear C i g*
      ((h : W (R := R) (I := R)).left ((h : W (R := R) (I := R)).right*i))⁻¹ at hc
  rw [hc]
  constructor
  · intro he
    have hc := congrArg (fun z => ((h : W (R := R) (I := R)).left ((h : W (R := R) (I := R)).right*i))⁻¹*z*
      (h : W (R := R) (I := R)).left ((h : W (R := R) (I := R)).right*i)) he
    simpa [mul_assoc] using hc
  · intro he
    rw [he,mul_one,mul_inv_cancel]

theorem localKernel_map_conjugate (h : C) (i : R) :
    (localKernel C i).map (MulAut.conjNormal h : MulAut (oddKernel C)).toMonoidHom=
      localKernel C ((h : W (R := R) (I := R)).right*i) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (conjugate_mem_iff C h x i).mpr hx
  · intro hg
    let a : MulAut (oddKernel C) := MulAut.conjNormal h
    have hx : a.symm g∈localKernel C i :=
      (conjugate_mem_iff C h (a.symm g) i).mp (by
        change a (a.symm g)∈localKernel C ((h : W (R := R) (I := R)).right*i)
        rw [a.apply_symm_apply]
        exact hg)
    exact ⟨a.symm g,hx,a.apply_symm_apply g⟩

variable (honto : Function.Surjective
  ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp C.subtype))

include honto in
theorem localKernel_card_eq (i j : R) :
    Nat.card (localKernel C i)=Nat.card (localKernel C j) := by
  obtain ⟨h,hh⟩ := honto (j*i⁻¹)
  have ht : (h : W (R := R) (I := R)).right*i=j := by change (h : W (R := R) (I := R)).right=j*i⁻¹ at hh; rw [hh]; group
  have hm := localKernel_map_conjugate C h i
  rw [ht] at hm
  rw [← hm]
  exact Nat.card_congr ((MulAut.conjNormal h).subgroupMap (localKernel C i)).toEquiv

include honto in
theorem equality_partition_invariant (r i j : R)
    (he : localKernel C i=localKernel C j) :
    localKernel C (r*i)=localKernel C (r*j) := by
  obtain ⟨h,hh⟩ := honto r
  change (h : W (R := R) (I := R)).right=r at hh
  have hi := localKernel_map_conjugate C h i
  have hj := localKernel_map_conjugate C h j
  rw [hh] at hi hj
  rw [← hi,← hj,he]

include honto in
theorem exists_colors
    (hne : ¬ ∀ i, localKernel C i=localKernel C 1) :
    ∃ color : R → Fin 2, ∀ i j, localKernel C i=localKernel C j →
      color i=color j → i=j :=
  RegularKleinKernelClassColoring.exists_two_color (localKernel C)
    (equality_partition_invariant C honto) hne

/-- If all local kernels agree, joint injectivity forces their common
kernel to vanish. Thus the actual odd layer embeds in one local cubic. -/
theorem rankOne_card (hO : oddKernel C≠⊥)
    (he : ∀ i, localKernel C i=localKernel C 1) : Nat.card (oddKernel C)=3 := by
  have hinj : Function.Injective (localLinear C (1 : R)) := by
    apply (localLinear C (1 : R)).ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply localLinear_joint C
    intro i
    have hi : g∈localKernel C i := (he i).symm ▸ hg
    simpa only [map_one] using hi
  let f : oddKernel C → {p : Equiv.Perm (Fin 3) // p^3=1} :=
    fun g => ⟨toThree (localLinear C 1 g),by rw [← map_pow,local_cubic,map_one]⟩
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
    (he : ∀ i, localKernel C i=localKernel C 1) : oddKernel C ≃* Cubic := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact mulEquivOfPrimeCardEq (rankOne_card C hO he)
    (by rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod])

end SymmetricSubgroupAsymptotics.BinaryPlaneKleinKernelGeometry
