import SymmetricSubgroupAsymptotics.WreathCycleGaugeConjugacy
import Mathlib.Algebra.Group.ConjFinite

/-! A coarse but uniform noncommutative wreath class code. Representatives
are used only to define an injection. There is no subgroup-monotonicity
claim and no replacement of the actual base by an abelian group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathCycleClassCode
open WreathCycleGaugeConjugacy
variable {C Q I : Type*} [Group C] [Group Q] [MulAction Q I]

abbrev Code (C Q I : Type*) [Group C] [One Q] :=
  (I → ConjClasses C) ⊕ ({q : Q // q ≠ 1} × ConjClasses C)

def elementCode (P : Q → (I → C) → C) (a : W (C := C) (Q := Q) (I := I)) :
    Code C Q I := by
  classical
  exact if h : a.right=1 then Sum.inl (fun i => ConjClasses.mk (a.left i))
    else Sum.inr (⟨a.right,h⟩,ConjClasses.mk (P a.right a.left))

theorem elementCode_eq_isConj (P : Q → (I → C) → C)
    (hP : ∀ q, q ≠ 1 → ∀ f g : I → C,
      IsConj (P q f) (P q g) →
        IsConj (⟨f,q⟩ : W (C := C) (I := I)) ⟨g,q⟩)
    (a b : W (C := C) (Q := Q) (I := I))
    (h : elementCode P a=elementCode P b) : IsConj a b := by
  classical
  by_cases ha : a.right=1 <;> by_cases hb : b.right=1
  · simp only [elementCode,dif_pos ha,dif_pos hb,Sum.inl.injEq] at h
    apply isConj_of_identity_coordinates a b ha hb
    intro i
    exact ConjClasses.mk_eq_mk_iff_isConj.mp (congrFun h i)
  · simp [elementCode,ha,hb] at h
  · simp [elementCode,ha,hb] at h
  · simp only [elementCode,dif_neg ha,dif_neg hb,Sum.inr.injEq,Prod.mk.injEq] at h
    have hq : a.right=b.right := congrArg Subtype.val h.1
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp h.2
    rcases a with ⟨f,q⟩
    rcases b with ⟨g,r⟩
    dsimp only at hq ha hc
    subst r
    exact hP q ha f g hc

def representative (c : ConjClasses (W (C := C) (Q := Q) (I := I))) :
    W (C := C) (Q := Q) (I := I) := Classical.choose (ConjClasses.exists_rep c)

theorem mk_representative (c : ConjClasses (W (C := C) (Q := Q) (I := I))) :
    ConjClasses.mk (representative c)=c := Classical.choose_spec (ConjClasses.exists_rep c)

theorem class_card_le [Finite C] [Finite Q] [Finite I]
    (P : Q → (I → C) → C)
    (hP : ∀ q, q ≠ 1 → ∀ f g : I → C,
      IsConj (P q f) (P q g) →
        IsConj (⟨f,q⟩ : W (C := C) (I := I)) ⟨g,q⟩) :
    Nat.card (ConjClasses (W (C := C) (Q := Q) (I := I))) ≤
      Nat.card (ConjClasses C)^Nat.card I + (Nat.card Q-1)*Nat.card (ConjClasses C) := by
  classical
  let code : ConjClasses (W (C := C) (Q := Q) (I := I)) → Code C Q I :=
    fun c => elementCode P (representative c)
  have hinj : Function.Injective code := by
    intro c d h
    have he := ConjClasses.mk_eq_mk_iff_isConj.mpr
      (elementCode_eq_isConj P hP (representative c) (representative d) h)
    simpa only [mk_representative] using he
  have hbound := Nat.card_le_card_of_injective code hinj
  have hq : Nat.card {q : Q // q ≠ 1}=Nat.card Q-1 := by
    letI := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun q : Q => q=1)
  simpa only [Code,Nat.card_sum,Nat.card_fun,Nat.card_prod,hq] using hbound

end SymmetricSubgroupAsymptotics.WreathCycleClassCode
