import SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles
import SymmetricSubgroupAsymptotics.SmallBinaryTopProperRelativeHead
import SymmetricSubgroupAsymptotics.OddDerivedKernelProperRelativeHead
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.TernaryLocalWreathProperRelativeHead
open SemidirectProduct
open TernaryLocalWreathNormalGenerators (Local Model localReflection)
abbrev Binary := TernarySwapUpperNormalGenerators.Binary
abbrev Upper := C2Wreath.W Binary
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fintype Local := Fintype.ofEquiv
  (TernarySwapUpperNormalGenerators.Ternary × Binary) SemidirectProduct.equivProd.symm
local instance : DecidableEq Local := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩; exact SemidirectProduct.ext hl hr
    · intro he; exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)
local instance : Fintype Model := Fintype.ofEquiv ((Local × Local) × Binary)
  SemidirectProduct.equivProd.symm
local instance : Fintype Upper := Fintype.ofEquiv ((Binary × Binary) × Binary)
  SemidirectProduct.equivProd.symm
local instance : DecidableEq Upper := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩; exact SemidirectProduct.ext hl hr
    · intro he; exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)
local instance : DecidableEq Model := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩; exact SemidirectProduct.ext hl hr
    · intro he; exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)

def projection : Model →* Upper := C2Wreath.mapLocal (rightHom : Local →* Binary)
theorem projection_surjective : Function.Surjective projection :=
  C2Wreath.mapLocal_surjective _ rightHom_surjective
def inversionLift : Model := inl (localReflection,localReflection)
theorem kernel_isPGroup : IsPGroup 3 projection.ker := by
  have hc : ∀ g : Model,projection g=1 → g^3=1 := by decide +kernel
  intro x
  refine ⟨1,?_⟩
  apply Subtype.ext
  change x.val^3=1
  exact hc _ x.property
theorem kernel_commutative : IsMulCommutative projection.ker := by
  have hc : ∀ g h : Model,projection g=1 → projection h=1 → g*h=h*g := by decide +kernel
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  exact hc _ _ x.property y.property
theorem kernel_le_derived : projection.ker≤commutator Model := by
  have hc : ∀ g : Model,projection g=1 → g=⁅g,inversionLift⁆^2 := by decide +kernel
  intro g hg
  rw [hc g hg]
  exact (commutator Model).pow_mem
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) 2

theorem upper_card : Nat.card Upper=8 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd : Upper ≃ (Binary × Binary) × Binary)]
  norm_num [Binary,TernarySwapUpperNormalGenerators.Binary,Nat.card_prod,Nat.card_eq_fintype_card]
theorem upper_center_card : Nat.card (Subgroup.center Upper)≤2 := by
  have hc : ∀ u : Upper,(∀ v : Upper,u*v=v*u) → u.right=1 ∧ u.left.1=u.left.2 := by decide +kernel
  let f : Subgroup.center Upper → Binary := fun u => u.val.left.1
  have hf : Function.Injective f := by
    intro u v he
    have hu := hc u.val (fun w => (Subgroup.mem_center_iff.mp u.property w).symm)
    have hv := hc v.val (fun w => (Subgroup.mem_center_iff.mp v.property w).symm)
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Prod.ext
      · exact he
      · exact hu.2.symm.trans (he.trans hv.2)
    · exact hu.1.trans hv.1.symm
  have h := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Binary=2 := by norm_num [Binary,TernarySwapUpperNormalGenerators.Binary,Nat.card_eq_fintype_card]
  exact h.trans hb.le

theorem proper_head (M : Subgroup Model) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  apply OddDerivedKernelProperRelativeHead.relative_head_le_one projection projection_surjective
    kernel_commutative kernel_le_derived kernel_isPGroup ?_ M hne
  intro L _ hL
  exact SmallBinaryTopProperRelativeHead.order_eight upper_card.le upper_center_card L hL

theorem isSolvable : IsSolvable Model := by
  have hU : IsPGroup 2 Upper := IsPGroup.of_card (n := 3) (by simpa using upper_card)
  letI : Group.IsNilpotent Upper := hU.isNilpotent
  letI : Group.IsNilpotent projection.ker := kernel_isPGroup.isNilpotent
  exact solvable_of_ker_le_range projection.ker.subtype projection (by rw [Subgroup.range_subtype])
end SymmetricSubgroupAsymptotics.TernaryLocalWreathProperRelativeHead
