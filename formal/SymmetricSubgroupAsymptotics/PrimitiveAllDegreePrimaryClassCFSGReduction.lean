import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeIsometryCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticSmallPrimaryClassBound

/-! Actual primary class codes close every remaining bounded B/C model.
The two binary rank-four D models remain literal, as do the existing
exceptional-model and large-degree residuals. The original action,
simple socle, subnormal subgroup and both degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreePrimaryClassCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .B _ _ _ | .C _ _ _ _ => False
  | i => PrimitiveAllDegreeIsometryCFSGReduction.RemainingBoundedPrimitiveParameters i

private theorem binary_order_eq_two (q : CFSG.PrimePower) (hprime : q.prime = 2)
    (hfour : ¬4 ≤ q.order) : q.order = 2 := by
  have he : q.exponent = 1 := by
    by_contra hh
    have htwo : 2 ≤ q.exponent := by have := q.exponent_pos; omega
    apply hfour
    change 4 ≤ q.prime ^ q.exponent
    rw [hprime]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) htwo
  change q.prime ^ q.exponent = 2
  rw [hprime, he, pow_one]

private theorem binary_order_eq_four (q : CFSG.PrimePower) (hprime : q.prime = 2)
    (hseven : q.order ≤ 7) (htwo : q.order ≠ 2) : q.order = 4 := by
  have he : q.exponent = 2 := by
    have hepos := q.exponent_pos
    have hone : q.exponent ≠ 1 := by
      intro h
      apply htwo
      change q.prime ^ q.exponent = 2
      rw [hprime, h, pow_one]
    have hthree : ¬3 ≤ q.exponent := by
      intro h
      have hh : 8 ≤ q.order := by
        change 2 ^ 3 ≤ q.prime ^ q.exponent
        rw [hprime]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h
      omega
    omega
  change q.prime ^ q.exponent = 4
  rw [hprime, he]
  rfl

theorem primitive_subnormal_cube_or_actual_remaining_parameters
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧
        ((Nat.card X < 1024 ∧ RemainingBoundedPrimitiveParameters i) ∨
          (1024 ≤ Nat.card X ∧ RemainingLargePrimitiveSimpleType i)) ∧
        ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a)) := by
  rcases PrimitiveAllDegreeIsometryCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case B r q hr =>
        change _ ∧ _ ∧ q.prime = 2 ∧ ¬(4 ≤ q.order ∨ 5 ≤ r) ∧ r ≠ 4 at hremaining
        obtain ⟨_,_,hp,hw,hnfour⟩ := hremaining
        have hrthree : r = 3 := by omega
        subst r
        have hq := binary_order_eq_two q hp (fun h => hw (Or.inl h))
        exact Or.inl (D.subnormal_class_cube_le_of_typeB_binary_rank_three q hq e H hH)
      case C r q hr hs =>
        change (r = 2 ∧ q.order ≤ 7 ∧ q.prime = 2) ∨
          (3 ≤ r ∧ _ ∧ q.prime = 2 ∧ ¬(4 ≤ q.order ∨ 5 ≤ r) ∧ r ≠ 4) at hremaining
        rcases hremaining with ⟨rfl,hq,hp⟩ | ⟨hthree,_,hp,hw,hnfour⟩
        · have hqfour := binary_order_eq_four q hp hq (hs rfl)
          exact Or.inl (D.subnormal_class_cube_le_of_typeC_four_rank_two q hqfour e H hH)
        · have hrthree : r = 3 := by omega
          subst r
          have hq := binary_order_eq_two q hp (fun h => hw (Or.inl h))
          exact Or.inl (D.subnormal_class_cube_le_of_typeC_binary_rank_three q hq e H hH)
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreePrimaryClassCFSGReduction
