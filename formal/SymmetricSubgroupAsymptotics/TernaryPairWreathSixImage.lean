import SymmetricSubgroupAsymptotics.TernaryLocalWreathSixFaithful
import SymmetricSubgroupAsymptotics.PrimePairWreathNormalGenerators
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryPairWreathSixImage
open SemidirectProduct
abbrev Ternary := TernarySwapUpperNormalGenerators.Ternary
abbrev Model := C2Wreath.W Ternary
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Finite SixPairLocalWreathSocles.Local := Finite.of_equiv
  (TernarySwapUpperNormalGenerators.Ternary × TernarySwapUpperNormalGenerators.Binary)
  SemidirectProduct.equivProd.symm
local instance : Finite SixPairLocalWreathSocles.Model := Finite.of_equiv
  ((SixPairLocalWreathSocles.Local × SixPairLocalWreathSocles.Local) ×
    TernarySwapUpperNormalGenerators.Binary) SemidirectProduct.equivProd.symm
local instance : Finite Model := Finite.of_equiv
  ((Ternary × Ternary) × TernarySwapUpperNormalGenerators.Binary) SemidirectProduct.equivProd.symm

local instance : DecidableEq Model := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩; exact SemidirectProduct.ext hl hr
    · intro he; exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)

def embed : Model →* SixPairLocalWreathSocles.Model :=
  C2Wreath.mapLocal (inl : Ternary →* SixPairLocalWreathSocles.Local)
def action : Model →* Equiv.Perm (Fin 6) := SixPairLocalWreathSocles.literalAction.comp embed

theorem embed_injective : Function.Injective embed := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Prod.ext
    · exact congrArg (fun z : SixPairLocalWreathSocles.Model => z.left.1.left) he
    · exact congrArg (fun z : SixPairLocalWreathSocles.Model => z.left.2.left) he
  · exact congrArg (fun z : SixPairLocalWreathSocles.Model => z.right) he

theorem action_injective : Function.Injective action :=
  TernaryLocalWreathSixFaithful.action_injective.comp embed_injective

def canonicalEquiv : Model ≃* action.range :=
  MulEquiv.ofBijective action.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),action.rangeRestrict_surjective⟩

theorem range_card : Nat.card action.range=18 := by
  rw [← Nat.card_congr canonicalEquiv.toEquiv,
    Nat.card_congr (SemidirectProduct.equivProd : Model ≃ (Ternary × Ternary) ×
      TernarySwapUpperNormalGenerators.Binary),Nat.card_prod,Nat.card_prod]
  norm_num [Ternary,TernarySwapUpperNormalGenerators.Ternary,
    TernarySwapUpperNormalGenerators.Binary,Nat.card_eq_fintype_card]

theorem isSolvable : IsSolvable action.range := by
  letI : IsSolvable SixPairLocalWreathSocles.Model := TernaryLocalWreathProperRelativeHead.isSolvable
  letI : IsSolvable Model := solvable_of_solvable_injective embed_injective
  exact solvable_of_surjective (f := canonicalEquiv.toMonoidHom) canonicalEquiv.surjective

theorem normal_generating_pairs : ∀ N : Subgroup action.range, N.Normal →
    ∃ x : Fin 2 → action.range, Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_tuples_of_surjective canonicalEquiv.toMonoidHom canonicalEquiv.surjective
    (PrimePairWreathNormalGenerators.normal_generating_pairs 3)

def rotation : Model := C2Wreath.firstFactor (Multiplicative.ofAdd 1)
def swap : Model := inr C2Wreath.gen

theorem generated_range {m : ℕ} (codes : Fin m → Model)
    (ht : action rotation ∈ Subgroup.closure (Set.range (fun i => action (codes i))))
    (hs : action swap ∈ Subgroup.closure (Set.range (fun i => action (codes i)))) :
    Subgroup.closure (Set.range (fun i => action (codes i)))=action.range := by
  let K := Subgroup.closure (Set.range (fun i => action (codes i)))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  · rintro _ ⟨g,rfl⟩
    change g ∈ K.comap action
    apply C2Wreath.mem_of_first_and_swap (K.comap action) ?_ hs g
    intro t
    have he : C2Wreath.firstFactor t=rotation^t.toAdd.val := by
      have h : ∀ x : ZMod 3, C2Wreath.firstFactor (Multiplicative.ofAdd x)=rotation^x.val := by
        decide +kernel
      exact h t.toAdd
    rw [he]
    exact (K.comap action).pow_mem ht _
end SymmetricSubgroupAsymptotics.TernaryPairWreathSixImage
