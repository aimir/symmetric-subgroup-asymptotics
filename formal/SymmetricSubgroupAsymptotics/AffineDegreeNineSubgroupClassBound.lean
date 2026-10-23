import SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import Mathlib.GroupTheory.PGroup

/-! Every original subgroup of a faithful degree-nine affine profile
has at most54 classes and satisfies GM. The actual order-nine regular
group is abelian by the prime-square theorem; its actual faithful
complement action and actual semidirect equivalence discharge all inputs.
No primitivity, elementary-abelian chart or catalogue is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassBound

local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A×B) SemidirectProduct.equivProd.symm
variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_card_le_fiftyFour (x : X) (hdegree : Nat.card X=9)
    (H : Subgroup G) : Nat.card (ConjClasses H) ≤ 54 := by
  have hV : Nat.card P.V=9 := (P.card_eq x).trans hdegree
  have hcomm : ∀ a b : P.V, a*b=b*a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3)
      (by simpa only [show (3 : ℕ)^2=9 by decide] using hV)
  letI : CommGroup P.V := { (inferInstance : Group P.V) with mul_comm := hcomm }
  let e := P.semidirectEquiv x
  let L := H.map e.symm.toMonoidHom
  letI : Finite L := Finite.of_injective (fun z : L => z.val) Subtype.val_injective
  letI : Finite (ConjClasses L) :=
    Finite.of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective
  let a := e.symm.subgroupMap H
  have hc : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses L) :=
    Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
      (ConjClasses.map_surjective a.symm.surjective)
  exact hc.trans (NineElementSemidirectSubgroupClassBound.subgroup_class_card_le_fiftyFour
    hV (P.complementAction x) (P.complementAction_injective x) L)

include P in
theorem subgroup_class_cube_le_garonziMaroti (x : X) (hdegree : Nat.card X=9)
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  calc
    Nat.card (ConjClasses H)^3 ≤ 54^3 :=
      Nat.pow_le_pow_left (subgroup_class_card_le_fiftyFour P x hdegree H) 3
    _ ≤ 5^(Nat.card X-1) := by rw [hdegree]; decide +kernel

end SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassBound
