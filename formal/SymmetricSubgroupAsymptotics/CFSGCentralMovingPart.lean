import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! Remove the points fixed by an entire normal subgroup, on the SAME
permutation carrier. Constant nonidentity fixed-point counts descend to
this invariant moving part by subtracting the common fixed subset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGCentralMovingPart
open MulAction
variable {G X : Type*} [Group G] [MulAction G X]

def MovingPart (C : Subgroup G) (X : Type*) [MulAction G X] :=
  {x : X // ¬ C ≤ stabilizer G x}

def FixedPart (C : Subgroup G) (X : Type*) [MulAction G X] :=
  {x : X // C ≤ stabilizer G x}

instance movingPartFinite [Finite X] (C : Subgroup G) : Finite (MovingPart C X) :=
  Finite.of_injective (fun x : MovingPart C X => x.val) Subtype.val_injective

instance fixedPartFinite [Finite X] (C : Subgroup G) : Finite (FixedPart C X) :=
  Finite.of_injective (fun x : FixedPart C X => x.val) Subtype.val_injective

theorem subgroup_stabilizer_smul_of_normal (C : Subgroup G) [C.Normal]
    (g : G) (x : X) (hx : C ≤ stabilizer G (g • x)) : C ≤ stabilizer G x := by
  intro c hc
  have hconj : g * c * g⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem c hc g
  have hh := hx hconj
  change (g * c * g⁻¹) • (g • x) = g • x at hh
  have he := congrArg (fun z : X => g⁻¹ • z) hh
  simpa only [mul_smul, inv_smul_smul] using he

instance movingPartAction (C : Subgroup G) [C.Normal] : MulAction G (MovingPart C X) where
  smul g x := ⟨g • x.val, fun hh => x.property (subgroup_stabilizer_smul_of_normal C g x.val hh)⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

theorem movingPart_no_whole_stabilizer (C : Subgroup G) [C.Normal] (x : MovingPart C X) :
    ¬ C ≤ stabilizer G x := by
  intro hh
  apply x.property
  intro c hc
  exact congrArg Subtype.val (hh hc)

def fixedByDecomposition (C : Subgroup G) [C.Normal] (c : C) :
    fixedBy X c ≃ FixedPart C X ⊕ fixedBy (MovingPart C X) c where
  toFun x := if hx : C ≤ stabilizer G x.val then Sum.inl ⟨x.val, hx⟩
    else Sum.inr ⟨⟨x.val, hx⟩, Subtype.ext x.property⟩
  invFun x := match x with
    | Sum.inl y => ⟨y.val, y.property c.property⟩
    | Sum.inr y => ⟨y.val.val, congrArg Subtype.val y.property⟩
  left_inv x := by
    by_cases hx : C ≤ stabilizer G x.val
    · simp only [dif_pos hx]
    · simp only [dif_neg hx]
  right_inv x := by
    rcases x with y | y
    · simp only [dif_pos y.property]
      rfl
    · simp only [dif_neg y.val.property]
      rfl

theorem fixedBy_movingPart_card [Finite X] (C : Subgroup G) [C.Normal] (c : C) :
    Nat.card (fixedBy (MovingPart C X) c) = Nat.card (fixedBy X c) - Nat.card (FixedPart C X) := by
  have he := Nat.card_congr (fixedByDecomposition (X := X) C c)
  rw [Nat.card_sum] at he
  omega

theorem constant_fixedBy_movingPart [Finite X] (C : Subgroup G) [C.Normal] (f : ℕ)
    (hfix : ∀ c : C, c ≠ 1 → Nat.card (fixedBy X c) = f) :
    ∀ c : C, c ≠ 1 → Nat.card (fixedBy (MovingPart C X) c) = f - Nat.card (FixedPart C X) := by
  intro c hc
  rw [fixedBy_movingPart_card, hfix c hc]

theorem exists_move_movingPart (C : Subgroup G) [C.Normal]
    (hmove : ∃ (c : C) (x : X), c • x ≠ x) :
    ∃ (c : C) (x : MovingPart C X), c • x ≠ x := by
  obtain ⟨c, x, hx⟩ := hmove
  have hx' : ¬ C ≤ stabilizer G x := fun hh => hx (hh c.property)
  refine ⟨c, ⟨x, hx'⟩, ?_⟩
  intro he
  exact hx (congrArg Subtype.val he)

theorem movingPart_card_le [Finite X] (C : Subgroup G) :
    Nat.card (MovingPart C X) ≤ Nat.card X :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end SymmetricSubgroupAsymptotics.CFSGCentralMovingPart
