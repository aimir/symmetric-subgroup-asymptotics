import SymmetricSubgroupAsymptotics.MarkedC4NilpotentPhysicalProductEncoding
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Literal supported permutation groups are canonically recovered from
subgroups on their retained physical slots. No counting premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.SupportedPermutationRestriction

private theorem mem_range_of_fixes {A B : Type} (ι : A ↪ B) (p : Equiv.Perm B)
    (hfix : ∀ x, x∉Set.range ι → p x=x) :
    p∈(Equiv.Perm.viaEmbeddingHom ι).range := by
  have hpreserve : ∀ x, p x∈Set.range ι ↔ x∈Set.range ι := by
    intro x
    constructor
    · intro hx
      by_contra hn
      exact hn ((hfix x hn) ▸ hx)
    · intro hx
      by_contra hn
      have hp := hfix (p x) hn
      have he : p x=x := p.injective hp
      exact hn (he.symm ▸ hx)
  let e : A ≃ Set.range ι := Equiv.ofInjective ι ι.injective
  let q : Equiv.Perm A := e.symm.permCongr (p.subtypePerm hpreserve)
  refine ⟨q,?_⟩
  apply Equiv.ext
  intro x
  by_cases hx : x∈Set.range ι
  · obtain ⟨a,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbeddingHom_apply,Equiv.Perm.viaEmbedding_apply]
    have he := congrArg Subtype.val
      (e.apply_symm_apply (p.subtypePerm hpreserve (e a)))
    exact he
  · rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,hfix x hx]

def slots {b : ℕ} (a : Fin (b+1)) : Fin a.val ↪ Fin (b+1) where
  toFun i := ⟨i.val+1,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change i.val+1=j.val+1 at hv
    exact Nat.add_right_cancel hv

def extension {b : ℕ} (a : Fin (b+1)) :
    Equiv.Perm (Fin a.val) →* Equiv.Perm (Fin (b+1)) :=
  Equiv.Perm.viaEmbeddingHom (slots a)

theorem supported_le_range {b : ℕ} (a : Fin (b+1))
    (P : Subgroup (Equiv.Perm (Fin (b+1))))
    (hP : NilpotentPhysicalProductEncoding.supported a.val P) :
    P≤(extension a).range := by
  intro p hp
  apply mem_range_of_fixes (slots a) p
  intro x hx
  apply hP p hp x
  by_contra hn
  push_neg at hn
  have hxpos : 0<x.val := by omega
  apply hx
  refine ⟨⟨x.val-1,by omega⟩,?_⟩
  apply Fin.ext
  change x.val-1+1=x.val
  omega

/-- Canonical restriction uses the actual inverse image under the slot
extension homomorphism. -/
def restrict {b : ℕ} (a : Fin (b+1))
    (P : Subgroup (Equiv.Perm (Fin (b+1)))) : Subgroup (Equiv.Perm (Fin a.val)) :=
  P.comap (extension a)

theorem recover {b : ℕ} (a : Fin (b+1))
    (P : Subgroup (Equiv.Perm (Fin (b+1))))
    (hP : NilpotentPhysicalProductEncoding.supported a.val P) :
    (restrict a P).map (extension a)=P :=
  Subgroup.map_comap_eq_self (supported_le_range a P hP)

theorem restrict_injective {b : ℕ} (a : Fin (b+1)) :
    Function.Injective (fun P : {P : Subgroup (Equiv.Perm (Fin (b+1))) //
      NilpotentPhysicalProductEncoding.supported a.val P} => restrict a P.1) := by
  intro P Q h
  apply Subtype.ext
  calc
    P.1 = (restrict a P.1).map (extension a) := (recover a P.1 P.2).symm
    _ = (restrict a Q.1).map (extension a) := congrArg (Subgroup.map (extension a)) h
    _ = Q.1 := recover a Q.1 Q.2

/-- The exact marked group, not just its order, is preserved by canonical
physical restriction. -/
def groupEquiv {b : ℕ} (a : Fin (b+1))
    (P : Subgroup (Equiv.Perm (Fin (b+1))))
    (hP : NilpotentPhysicalProductEncoding.supported a.val P) : restrict a P ≃* P :=
  ((restrict a P).equivMapOfInjective (extension a)
    (Equiv.Perm.viaEmbeddingHom_injective (slots a))).trans
      (MulEquiv.subgroupCongr (recover a P hP))

theorem hom_card_eq {b : ℕ} (a : Fin (b+1))
    (P : Subgroup (Equiv.Perm (Fin (b+1))))
    (hP : NilpotentPhysicalProductEncoding.supported a.val P) :
    Nat.card (P →* Multiplicative (ZMod 4))=
      Nat.card (restrict a P →* Multiplicative (ZMod 4)) :=
  Nat.card_congr (homPrecompEquiv (groupEquiv a P hP))
end SymmetricSubgroupAsymptotics.MarkedC4.SupportedPermutationRestriction
