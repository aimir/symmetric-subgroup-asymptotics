import SymmetricSubgroupAsymptotics.BinaryRegularKleinWreathCoordinates
import SymmetricSubgroupAsymptotics.DihedralEightInjectedNormalGenerators

/-! A faithful D8 action on four blocks, with a literal regular Klein
subgroup. All finite checks concern eight group elements and four points. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.DihedralEightRegularKleinBlockModel
abbrev R := BinaryRegularKleinWreath.R
abbrev Q := DihedralGroup 4
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private def label : R ≃ ZMod 4 where
  toFun x := 2*(x.toAdd 0).val+(x.toAdd 1).val
  invFun x := Multiplicative.ofAdd ![(x.val/2 : ℕ),(x.val%2 : ℕ)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def applyPoint : Q → ZMod 4 → ZMod 4
  | .r i,x => x+i
  | .sr i,x => -x-i

private def permutation (q : Q) : Equiv.Perm (ZMod 4) where
  toFun := applyPoint q
  invFun := applyPoint q⁻¹
  left_inv := by intro x; revert q x; decide +kernel
  right_inv := by intro x; revert q x; decide +kernel

private def permutationHom : Q →* Equiv.Perm (ZMod 4) where
  toFun := permutation
  map_one' := by apply Equiv.ext; intro x; revert x; decide +kernel
  map_mul' q h := by apply Equiv.ext; intro x; revert q h x; decide +kernel

def action : Q →* Equiv.Perm R :=
  label.symm.permCongrHom.toMonoidHom.comp permutationHom

instance : MulAction Q R := MulAction.compHom R action

/-- Actual regular block translations inside D8. -/
def regular : R →* Q where
  toFun x := if x.toAdd 1=0 then .r (2*(x.toAdd 0).val)
    else .sr (3+2*(x.toAdd 0).val)
  map_one' := by decide +kernel
  map_mul' x y := by revert x y; decide +kernel

@[simp] theorem regular_smul (r i : R) : regular r • i=r*i := by
  revert r i
  decide +kernel

theorem regular_injective : Function.Injective regular := by
  intro r s h
  have he := congrArg (fun q : Q => q • (1 : R)) h
  simpa only [regular_smul,mul_one] using he

theorem action_injective : Function.Injective action := by
  intro q h he
  have hp : ∀ i, action q i=action h i := fun i => congrArg (fun f => f i) he
  have ht : ∀ q h : Q, (∀ i : R, action q i=action h i) → q=h := by
    decide +kernel
  exact ht q h hp

instance : FaithfulSMul Q R :=
  ⟨fun {q h} he => action_injective (Equiv.ext he)⟩

theorem binary : IsPGroup 2 Q := by
  apply IsPGroup.of_card (n := 3)
  exact DihedralGroup.nat_card.trans (by norm_num)

/-- The full preimage of regular.range in any onto block image still
maps onto every regular block translation. -/
theorem regular_preimage_surjective {G : Type} [Group G]
    (top : G →* Q) (htop : Function.Surjective top) :
    Function.Surjective
      ((top.comp (Subgroup.comap top regular.range).subtype).codRestrict
        regular.range (fun g => g.property)) := by
  intro q
  obtain ⟨g,hg⟩ := htop q
  refine ⟨⟨g,?_⟩,?_⟩
  · change top g∈regular.range
    rw [hg]
    exact q.property
  · exact Subtype.ext hg

end SymmetricSubgroupAsymptotics.DihedralEightRegularKleinBlockModel
