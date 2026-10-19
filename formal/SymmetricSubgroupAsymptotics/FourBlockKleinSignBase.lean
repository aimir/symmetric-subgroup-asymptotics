import SymmetricSubgroupAsymptotics.TernaryFourBlockKleinSocles
import SymmetricSubgroupAsymptotics.FourBlockBinarySignSpaces

/-! The actual regular Klein block action in both retained coordinate
charts. Two displayed involutions generate it, and one involution has
two point orbits, giving uniform binary permutation bound two. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FourBlockKleinSignBase

open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block)
open SemidirectProduct

abbrev Base := TernaryFourBlockKleinSocles.Complement
abbrev Bit := TernaryFourBlockKleinSocles.Bit

def first : Base := (Multiplicative.ofAdd 1,1)
def second : Base := (1,Multiplicative.ofAdd 1)

def blockEquiv : Block ≃ Fin 4 where
  toFun i := i.toAdd
  invFun i := Multiplicative.ofAdd i
  left_inv _ := rfl
  right_inv _ := rfl

def blocks : Base →* Equiv.Perm (Fin 4) :=
  blockEquiv.permCongrHom.toMonoidHom.comp TernaryFourBlockKleinSocles.blockAction

instance blockAction : MulAction Base (Fin 4) := MulAction.compHom (Fin 4) blocks

theorem transitive : ∀ i : Fin 4, ∃ g : Base, g • (0 : Fin 4) = i := by
  intro i
  refine ⟨TernaryFourBlockKleinSocles.orbitElement (Multiplicative.ofAdd i),?_⟩
  revert i
  decide +kernel

theorem base_mem (K : Subgroup Base) (hfirst : first ∈ K) (hsecond : second ∈ K)
    (g : Base) : g ∈ K := by
  have he (b : Bit) : (Multiplicative.ofAdd (1 : ZMod 2))^b.toAdd.val = b := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow,nsmul_eq_mul]
  have hg : first^g.1.toAdd.val * second^g.2.toAdd.val = g := by
    apply Prod.ext
    · change (Multiplicative.ofAdd (1 : ZMod 2))^g.1.toAdd.val * 1^g.2.toAdd.val = g.1
      rw [one_pow,mul_one,he]
    · change (1 : Bit)^g.1.toAdd.val * (Multiplicative.ofAdd (1 : ZMod 2))^g.2.toAdd.val = g.2
      rw [one_pow,one_mul,he]
  rw [← hg]
  exact K.mul_mem (K.pow_mem hfirst _) (K.pow_mem hsecond _)

theorem image_mem {G : Type} [Group G] (f : Base →* G) (K : Subgroup G)
    (hfirst : f first ∈ K) (hsecond : f second ∈ K) (g : Base) : f g ∈ K :=
  base_mem (K.comap f) hfirst hsecond g

theorem uniform_two : UniformSubrepresentationGeneratorBound
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation
      (R := Base) (X := Fin 4)) 2 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    first (fun j : Fin 2 => if j = 0 then 0 else 2)
  intro i
  refine ⟨⟨i.val / 2,by omega⟩,i.val % 2,?_⟩
  revert i
  decide +kernel

theorem normalGen (K : Subgroup Base) (hK : K.Normal) : MarkedC4.normalGen K ≤ 2 :=
  TernaryFourBlockKleinSocles.complement_normalGen K hK

theorem coprime : Nat.Coprime 3 (Nat.card Base) :=
  TernaryFourBlockKleinSocles.complement_coprime

end SymmetricSubgroupAsymptotics.FourBlockKleinSignBase

end
