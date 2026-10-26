import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenRecoverA
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenRecoverB
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWordPowers
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration

/-! The two selected actual11-words recover both original pinned
generators. Their genuine cyclic11-subgroups therefore generate the SAME
original subgroup, and extend to two actual conjugate Sylow11 subgroups.
The finite word certificates, rather than the diagnostic, supply every
recovery and whole-permutation power identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenGeneration
open CFSG.Models.Mathieu22Construction CFSGMathieuTwentyTwoElevenWords

private abbrev H : Subgroup (Equiv.Perm (Fin 22)) := Subgroup.closure ({a,b} : Set _)

def originalA : CFSG.Models.Mathieu22 := ⟨a,Subgroup.subset_closure (Or.inl rfl)⟩
def originalB : CFSG.Models.Mathieu22 := ⟨b,Subgroup.subset_closure (Or.inr rfl)⟩
def firstElement : CFSG.Models.Mathieu22 := originalA^3*originalB^2
def secondElement : CFSG.Models.Mathieu22 := originalA*firstElement*originalA⁻¹

theorem firstElement_pow_eleven : firstElement^11=1 := by
  apply Subtype.ext
  exact firstWord_pow_eleven

theorem secondElement_pow_eleven : secondElement^11=1 := by
  apply Subtype.ext
  exact secondWord_pow_eleven

theorem recover_originalA : recoverA firstElement secondElement=originalA := by
  apply Subtype.ext
  exact recoverA_eq

theorem recover_originalB : recoverB firstElement secondElement=originalB := by
  apply Subtype.ext
  exact recoverB_eq

theorem zpowers_sup_eq_top :
    Subgroup.zpowers firstElement⊔Subgroup.zpowers secondElement=⊤ := by
  let R := Subgroup.zpowers firstElement⊔Subgroup.zpowers secondElement
  have hx : firstElement∈R := Subgroup.mem_sup_left (Subgroup.mem_zpowers firstElement)
  have hy : secondElement∈R := Subgroup.mem_sup_right (Subgroup.mem_zpowers secondElement)
  have ha : originalA∈R := by
    rw [←recover_originalA]
    exact recoverA_mem R firstElement secondElement hx hy
  have hb : originalB∈R := by
    rw [←recover_originalB]
    exact recoverB_mem R firstElement secondElement hx hy
  have hmap : H≤R.map H.subtype := by
    change Subgroup.closure ({a,b} : Set _)≤R.map H.subtype
    apply (Subgroup.closure_le (R.map H.subtype)).mpr
    rintro z (rfl|rfl)
    · exact ⟨originalA,ha,rfl⟩
    · exact ⟨originalB,hb,rfl⟩
  apply top_unique
  intro g _
  obtain ⟨z,hz,he⟩ := hmap g.property
  have heq : z=g := Subtype.ext he
  exact heq ▸ hz

private theorem zpowers_isPGroup_of_eleven_power {G : Type*} [Group G]
    (x : G) (hx : x^11=1) : IsPGroup 11 (Subgroup.zpowers x) := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hd : Nat.card (Subgroup.zpowers x)∣11 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx
  rcases (show Nat.Prime 11 by decide).eq_one_or_self_of_dvd _ hd with h|h
  · exact IsPGroup.of_card (n:=0) (by simpa only [pow_zero] using h)
  · exact IsPGroup.of_card (n:=1) (by simpa only [pow_one] using h)

theorem two_conjugate_sylows :
    ∃ (P : Sylow 11 CFSG.Models.Mathieu22) (g : CFSG.Models.Mathieu22),
      Subgroup.closure ((P : Set CFSG.Models.Mathieu22) ∪
        (P : Subgroup CFSG.Models.Mathieu22).map (MulAut.conj g).toMonoidHom)=⊤ := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨P,g,_,hg⟩ := CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows
    (Subgroup.zpowers firstElement) (Subgroup.zpowers secondElement)
    (zpowers_isPGroup_of_eleven_power firstElement firstElement_pow_eleven)
    (zpowers_isPGroup_of_eleven_power secondElement secondElement_pow_eleven)
    zpowers_sup_eq_top
  exact ⟨P,g,hg⟩

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenGeneration
