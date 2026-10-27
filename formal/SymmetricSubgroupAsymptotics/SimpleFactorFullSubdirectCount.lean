import SymmetricSubgroupAsymptotics.FullSubdirectGoursat
import SymmetricSubgroupAsymptotics.SimplePowerEpimorphismCount
import Mathlib.GroupTheory.Subgroup.Simple

/-! Complete nonabelian-simple coordinate attachment count. Literal Goursat
axes and every epimorphism twist are charged. No diagonal type or kernel-only
classification replaces the full subgroup. Factor2 is harmless overcount. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SimpleFactorFullSubdirectCount
open FullSubdirectGoursat

variable {T B : Type} [Group T] [Finite T] [IsSimpleGroup T] [Group B] [Finite B]

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
local instance homFinite {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) := Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective
local instance quotientFinite (N : NormalAxis T) : Finite (T ⧸ N.val) :=
  Finite.of_surjective (QuotientGroup.mk' N.val) (QuotientGroup.mk'_surjective N.val)

private theorem normalAxis_card_le_two : Nat.card (NormalAxis T) ≤ 2 := by
  letI : Fintype (NormalAxis T) := Fintype.ofFinite _
  let z : NormalAxis T := ⟨⊥,inferInstance⟩
  let t : NormalAxis T := ⟨⊤,inferInstance⟩
  have hs : Finset.univ ⊆ ({z,t} : Finset (NormalAxis T)) := by
    intro N _
    rcases N.property.eq_bot_or_eq_top with hb | ht
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hb))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext ht)))
  have hc : ({z,t} : Finset (NormalAxis T)).card ≤ 2 := by
    have hh := Finset.card_insert_le z ({t} : Finset (NormalAxis T))
    simpa only [Finset.card_singleton] using hh
  have hh := (Finset.card_le_card hs).trans hc
  simpa only [Finset.card_univ,Nat.card_eq_fintype_card] using hh

private theorem quotient_epi_card_le (N : NormalAxis T) :
    Nat.card (GroupEpimorphism B (T ⧸ N.val)) ≤ 1+Nat.card (GroupEpimorphism B T) := by
  obtain ⟨N,hN⟩ := N
  letI : N.Normal := hN
  rcases hN.eq_bot_or_eq_top with hb | ht
  · subst N
    have he := fusionGroupEpimorphism_card_congr (MulEquiv.refl B)
      (QuotientGroup.quotientBot : T ⧸ (⊥ : Subgroup T) ≃* T)
    exact he.le.trans (Nat.le_add_left _ _)
  · subst N
    letI : Subsingleton (T ⧸ (⊤ : Subgroup T)) := QuotientGroup.subsingleton_quotient_top
    letI : Subsingleton (GroupEpimorphism B (T ⧸ (⊤ : Subgroup T))) := ⟨by
      intro f g
      apply Subtype.ext
      ext b
      exact Subsingleton.elim _ _⟩
    have hh := Nat.card_le_card_of_injective
      (fun _ : GroupEpimorphism B (T ⧸ (⊤ : Subgroup T)) => ())
      (fun _ _ _ => Subsingleton.elim _ _)
    have h1 : Nat.card (GroupEpimorphism B (T ⧸ (⊤ : Subgroup T))) ≤ 1 := by
      simpa only [Nat.card_unique] using hh
    exact h1.trans (Nat.le_add_right _ _)

theorem card_full_le : Nat.card (Full T B) ≤ 2*(1+Nat.card (GroupEpimorphism B T)) := by
  letI : Fintype (NormalAxis T) := Fintype.ofFinite _
  calc
    Nat.card (Full T B) ≤ Nat.card (Data T B) :=
      Nat.card_le_card_of_injective (FullSubdirectGoursat.code (A := T) (B := B))
        FullSubdirectGoursat.code_injective
    _ = ∑ N : NormalAxis T,Nat.card (GroupEpimorphism B (T ⧸ N.val)) := Nat.card_sigma
    _ ≤ ∑ _N : NormalAxis T,(1+Nat.card (GroupEpimorphism B T)) :=
      Finset.sum_le_sum (fun N _ => quotient_epi_card_le (B := B) N)
    _ = Nat.card (NormalAxis T)*(1+Nat.card (GroupEpimorphism B T)) := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ 2*(1+Nat.card (GroupEpimorphism B T)) :=
      Nat.mul_le_mul_right _ normalAxis_card_le_two

/-- The complete attachment fibre has only a linear coordinate/twist cost
when its original tail embeds in b copies of this actual simple factor. -/
theorem card_full_le_of_tail_embedding (hZ : IsCenterless T)
    (b : ℕ) (rho : B →* (Fin b → T)) (hrho : Function.Injective rho) :
    (Nat.card (Full T B) : ℝ) ≤ 2*(1+(b : ℝ)*Nat.card (T ≃* T)) := by
  have hh : (Nat.card (Full T B) : ℝ) ≤ 2*(1+(Nat.card (GroupEpimorphism B T) : ℝ)) := by
    exact_mod_cast (card_full_le (T := T) (B := B))
  have he := SimplePowerEpimorphismCount.card_le_of_embedding hZ b rho hrho
  linarith only [hh,he]

end SymmetricSubgroupAsymptotics.SimpleFactorFullSubdirectCount
