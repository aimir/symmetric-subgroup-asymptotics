import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerived
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Index

/-! The actual positive group and fixed torus form a faithful semidirect
product inside the original Ree fixed group. Its order is q^3(q-1), and
it is soluble. No normalizer equality or Bruhat theorem is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalBorel
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveDerived

def torusNormalizerHom (m : ℕ) : (Field m)ˣ →*
    Subgroup.normalizer (fixedPositiveGroup m : Set (originalModelFixed m)) :=
  (fixedTorusHom m).codRestrict _ (fixedTorus_mem_normalizer m)

def torusActionHom (m : ℕ) : (Field m)ˣ →* MulAut (fixedPositiveGroup m) :=
  (fixedPositiveGroup m).normalizerMonoidHom.comp (torusNormalizerHom m)

theorem torusActionHom_apply (m : ℕ) (t : (Field m)ˣ) :
    torusActionHom m t=fixedPositiveTorusAut m t := rfl

abbrev BorelSource (m : ℕ) := fixedPositiveGroup m ⋊[torusActionHom m] (Field m)ˣ

def borelHom (m : ℕ) : BorelSource m →* originalModelFixed m :=
  SemidirectProduct.lift (φ := torusActionHom m) (fixedPositiveGroup m).subtype
    (fixedTorusHom m) (by
      intro t
      apply MonoidHom.ext
      intro u
      exact fixedPositiveTorusAut_val m t u)

theorem borelHom_apply (m : ℕ) (x : BorelSource m) :
    borelHom m x=x.left.val*fixedTorusHom m x.right := rfl

theorem positive_inf_torus_eq_bot (m : ℕ) :
    fixedPositiveGroup m ⊓ (fixedTorusHom m).range=⊥ := by
  apply Subgroup.inf_eq_bot_of_coprime
  rw [fixedPositiveGroup_card,fixedTorus_card]
  apply (Nat.coprime_pow_left_iff (by decide : 0<3) _ _).mpr
  exact (Nat.coprime_self_sub_right
    (Nat.pow_le_pow_right (by decide : 1≤3) (Nat.zero_le (2*m+1)) :
      1≤3^(2*m+1))).mpr
    (Nat.coprime_one_right _)

theorem borelHom_injective (m : ℕ) : Function.Injective (borelHom m) := by
  apply (borelHom m).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have he : x.left.val*fixedTorusHom m x.right=1 := hx
  have hl : x.left.val=(fixedTorusHom m x.right)⁻¹ := by
    calc
      _=x.left.val*fixedTorusHom m x.right*(fixedTorusHom m x.right)⁻¹ := by simp
      _=_ := by rw [he,one_mul]
  have hm : x.left.val∈fixedPositiveGroup m ⊓ (fixedTorusHom m).range := by
    refine ⟨x.left.property,?_⟩
    exact ⟨x.right⁻¹,by rw [map_inv,hl]⟩
  rw [positive_inf_torus_eq_bot] at hm
  have hlone : x.left.val=1 := hm
  have hrone : x.right=1 := by
    apply fixedTorusHom_injective m
    simpa only [hlone,one_mul,map_one] using he
  apply Subgroup.mem_bot.mpr
  apply SemidirectProduct.ext
  · exact Subtype.ext hlone
  · exact hrone

def borelGroup (m : ℕ) : Subgroup (originalModelFixed m) := (borelHom m).range

theorem borelGroup_card (m : ℕ) :
    Nat.card (borelGroup m)=(3^(2*m+1))^3*(3^(2*m+1)-1) := by
  have hc : Nat.card (BorelSource m)=Nat.card (borelGroup m) :=
    Nat.card_congr (Equiv.ofInjective (borelHom m) (borelHom_injective m))
  rw [←hc,SemidirectProduct.card,fixedPositiveGroup_card,Nat.card_units,field_card]

theorem borelSource_soluble (m : ℕ) : IsSolvable (BorelSource m) := by
  letI : Finite (fixedPositiveGroup m) :=
    Finite.of_equiv (Fin 3 → Field m) (fixedPositiveEquiv m)
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Group.IsNilpotent (fixedPositiveGroup m) :=
    (fixedPositiveGroup_isPGroup m).isNilpotent
  apply solvable_of_ker_le_range
    (SemidirectProduct.inl (φ := torusActionHom m))
    (SemidirectProduct.rightHom (φ := torusActionHom m))
  intro x hx
  refine ⟨x.left,?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact hx.symm

theorem borelGroup_soluble (m : ℕ) : IsSolvable (borelGroup m) := by
  letI : IsSolvable (BorelSource m) := borelSource_soluble m
  apply solvable_of_surjective (f := (borelHom m).rangeRestrict)
  rintro ⟨g,⟨x,rfl⟩⟩
  exact ⟨x,rfl⟩

theorem borelGroup_le_normalizer (m : ℕ) :
    borelGroup m≤Subgroup.normalizer (fixedPositiveGroup m : Set (originalModelFixed m)) := by
  rintro g ⟨x,rfl⟩
  rw [borelHom_apply]
  exact (Subgroup.normalizer _).mul_mem
    ((fixedPositiveGroup m).le_normalizer x.left.property) (fixedTorus_mem_normalizer m x.right)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalBorel
