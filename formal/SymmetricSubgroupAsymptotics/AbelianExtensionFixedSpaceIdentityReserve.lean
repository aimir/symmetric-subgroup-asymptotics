import SymmetricSubgroupAsymptotics.AbelianExtensionFixedSpaceClassBound

/-! A four-unit identity reserve in an ORIGINAL nonsplit abelian
extension is absorbed by the actual quotient order. All fixed-point
bounds concern its literal quotient conjugation action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianExtensionFixedSpaceIdentityReserve
open AbelianExtensionConjugation
variable {G : Type*} [Group G] [Finite G]

theorem class_card_le_class_add_one_mul
    (N : Subgroup G) [N.Normal] [IsMulCommutative N] (T : ℕ)
    (hquotient : 4≤Nat.card (G ⧸ N)) (hsize : Nat.card N≤4*T)
    (hfixed : ∀ q : G ⧸ N, q≠1 →
      Nat.card {n : N // quotientConjugation N q n=n}≤T) :
    Nat.card (ConjClasses G)≤(Nat.card (ConjClasses (G ⧸ N))+1)*T := by
  have h := AbelianExtensionFixedSpaceClassBound.class_card_mul_quotient_le N T hfixed
  have hsize' : Nat.card N≤Nat.card (G ⧸ N)*T :=
    hsize.trans (Nat.mul_le_mul_right T hquotient)
  have hb : Nat.card (G ⧸ N)*Nat.card (ConjClasses G)≤
      Nat.card (G ⧸ N)*((Nat.card (ConjClasses (G ⧸ N))+1)*T) := by
    apply h.trans
    calc
      Nat.card N+T*(Nat.card (G ⧸ N)*Nat.card (ConjClasses (G ⧸ N)))≤
          Nat.card (G ⧸ N)*T+T*(Nat.card (G ⧸ N)*Nat.card (ConjClasses (G ⧸ N))) :=
        Nat.add_le_add_right hsize' _
      _=_ := by ring
  exact Nat.le_of_mul_le_mul_left hb (Nat.card_pos (α:=G ⧸ N))

end SymmetricSubgroupAsymptotics.AbelianExtensionFixedSpaceIdentityReserve
