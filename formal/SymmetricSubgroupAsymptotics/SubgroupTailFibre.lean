import SymmetricSubgroupAsymptotics.SubdirectTailImage

/-! Exact decomposition by the literal second-coordinate image. There is
no fullness requirement on the first group. Conditions on its individual
coordinates, and all survival predicates, are retained on the decoded
original subgroup. No counting estimate or physical weight is an input.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.SubgroupTailFibre

open SubdirectTailImage

variable {A B : Type*} [Group A] [Group B]

theorem core_map_snd_eq_top (K : Subgroup (A × B)) :
    (core K).map (MonoidHom.snd A (tail K)) = ⊤ := by
  apply top_unique
  intro b _
  obtain ⟨k,hk⟩ := core_snd_surjective K b
  exact Subgroup.mem_map.mpr ⟨k.1,k.2,hk⟩

/-- A second-full subgroup of A × L recovers exactly L after its literal
inclusion into A × B. No surjectivity onto A is required. -/
theorem tail_map_inclusion (L : Subgroup B) (J : Subgroup (A × L))
    (hJ : J.map (MonoidHom.snd A L) = ⊤) :
    tail (J.map (inclusion L)) = L := by
  unfold tail
  rw [Subgroup.map_map]
  ext b
  constructor
  · rintro ⟨⟨a,l⟩,_,rfl⟩
    exact l.2
  · intro hb
    have hl : (⟨b,hb⟩ : L) ∈ J.map (MonoidHom.snd A L) := by
      rw [hJ]
      trivial
    obtain ⟨⟨a,l⟩,hj,he⟩ := Subgroup.mem_map.mp hl
    refine Subgroup.mem_map.mpr ⟨(a,l),hj,?_⟩
    change (l : B) = b
    exact congrArg Subtype.val he

abbrev OriginalFamily (S : Subgroup B → Prop) (P : Subgroup (A × B) → Prop) :=
  {K : Subgroup (A × B) // S (tail K) ∧ P K}

/-- Each fibre uses the actual subgroup L, with its inherited group
structure, and the original predicate applied after exact reconstruction. -/
abbrev CoreFamily (S : Subgroup B → Prop) (P : Subgroup (A × B) → Prop) :=
  Σ L : {L : Subgroup B // S L},
    {J : Subgroup (A × L.1) //
      J.map (MonoidHom.snd A L.1) = ⊤ ∧ P (J.map (inclusion L.1))}

variable (S : Subgroup B → Prop) (P : Subgroup (A × B) → Prop)

def code (K : OriginalFamily S P) : CoreFamily S P :=
  ⟨⟨tail K.1,K.2.1⟩,⟨core K.1,core_map_snd_eq_top K.1,by
    rw [core_map]
    exact K.2.2⟩⟩

def decode (d : CoreFamily S P) : OriginalFamily S P :=
  ⟨d.2.1.map (inclusion d.1.1),by
    rw [tail_map_inclusion d.1.1 d.2.1 d.2.2.1]
    exact d.1.2,d.2.2.2⟩

@[simp] theorem code_tail (K : OriginalFamily S P) :
    (code S P K).1.1 = tail K.1 := rfl

@[simp] theorem decode_val (d : CoreFamily S P) :
    (decode S P d).1 = d.2.1.map (inclusion d.1.1) := rfl

@[simp] theorem decode_code (K : OriginalFamily S P) :
    decode S P (code S P K) = K :=
  Subtype.ext (core_map K.1)

theorem decode_injective : Function.Injective (decode S P) := by
  rintro ⟨L,J⟩ ⟨L',J'⟩ he
  have hK : J.1.map (inclusion L.1) = J'.1.map (inclusion L'.1) :=
    congrArg Subtype.val he
  have hL : L = L' := by
    apply Subtype.ext
    calc
      L.1 = tail (J.1.map (inclusion L.1)) :=
        (tail_map_inclusion L.1 J.1 J.2.1).symm
      _ = tail (J'.1.map (inclusion L'.1)) := congrArg tail hK
      _ = L'.1 := tail_map_inclusion L'.1 J'.1 J'.2.1
  subst L'
  have hJ : J = J' := Subtype.ext
    (Subgroup.map_injective (inclusion_injective L.1) hK)
  subst J'
  rfl

@[simp] theorem code_decode (d : CoreFamily S P) :
    code S P (decode S P d) = d := by
  apply decode_injective S P
  exact decode_code S P (decode S P d)

/-- The actual tail and second-full core form an exact parametrization,
even when projection onto the entire first group is proper. -/
def equiv : OriginalFamily S P ≃ CoreFamily S P where
  toFun := code S P
  invFun := decode S P
  left_inv := decode_code S P
  right_inv := code_decode S P

section Finite

variable [Finite A] [Finite B]

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- Exact fibre multiplicity, with the unique actual tail retained. -/
theorem card_eq_sum :
    Nat.card (OriginalFamily S P) =
      ∑ L : {L : Subgroup B // S L},
        Nat.card {J : Subgroup (A × L.1) //
          J.map (MonoidHom.snd A L.1) = ⊤ ∧ P (J.map (inclusion L.1))} := by
  rw [Nat.card_congr (equiv S P), Nat.card_sigma]

/-- Any weight on the complete original subgroup is evaluated after
literal decoding. No product factorization or invariance is assumed. -/
theorem sum_eq_sum {M : Type*} [AddCommMonoid M]
    (W : Subgroup (A × B) → M) :
    (∑ K : OriginalFamily S P, W K.1) =
      ∑ L : {L : Subgroup B // S L},
        ∑ J : {J : Subgroup (A × L.1) //
          J.map (MonoidHom.snd A L.1) = ⊤ ∧ P (J.map (inclusion L.1))},
          W (J.1.map (inclusion L.1)) := by
  calc
    _ = ∑ d : CoreFamily S P, W (decode S P d).1 := by
      apply Fintype.sum_equiv (equiv S P)
      intro K
      change W K.1 = W (decode S P (code S P K)).1
      rw [decode_code]
    _ = _ := Fintype.sum_sigma _

end Finite
end SymmetricSubgroupAsymptotics.SubgroupTailFibre
