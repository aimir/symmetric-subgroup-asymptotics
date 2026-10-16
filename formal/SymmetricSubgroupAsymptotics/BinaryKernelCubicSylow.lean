import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Original Sylow data above a literal A4/S4 quotient with binary
kernel. The target's order determines its Sylow order, while disjoint
prime-power kernels make the original Sylow map injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryKernelCubicSylow
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G H : Type} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (P : Sylow 3 G)

include hker in
theorem restriction_injective : Function.Injective (f.comp (P : Subgroup G).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff (f.comp (P : Subgroup G).subtype)).mp
  apply le_antisymm
  · intro x hx
    have hxker : (x : G) ∈ f.ker := hx
    have hxone : (x : G) = 1 := Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_ne 3 2 (by decide) (P : Subgroup G) f.ker P.isPGroup' hker)
      x.2 hxker
    exact Subgroup.mem_bot.mpr (Subtype.ext hxone)
  · exact bot_le

include hf hker in
theorem card_three (hH : Nat.card H = 12 ∨ Nat.card H = 24) : Nat.card P = 3 := by
  letI : Finite H := Finite.of_surjective f hf
  let image : P →* (P : Subgroup G).map f :=
    { toFun := fun x => ⟨f x.1,⟨x.1,x.2,rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x.1 y.1) }
  have hi : Function.Injective image := by
    intro x y h
    exact restriction_injective f hker P (congrArg Subtype.val h)
  have hs : Function.Surjective image := by
    rintro ⟨y,x,hx,hxy⟩
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  let e := MulEquiv.ofBijective image ⟨hi,hs⟩
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (P.mapSurjective hf) = 3
  rw [Sylow.card_eq_multiplicity]
  rcases hH with h | h
  · rw [h,show Nat.factorization 12 3 = 1 by decide +kernel,pow_one]
  · rw [h,show Nat.factorization 24 3 = 1 by decide +kernel,pow_one]

end SymmetricSubgroupAsymptotics.BinaryKernelCubicSylow
