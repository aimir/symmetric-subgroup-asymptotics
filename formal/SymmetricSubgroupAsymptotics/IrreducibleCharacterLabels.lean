import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Group.ConjFinite

/-! Irreducible character labels of original epimorphisms. Surjective
pullback preserves irreducibility, and distinct irreducible characters
are independent in the space of functions on the original conjugacy
classes. No conjugacy-class bound for a quotient action is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
variable {k G H V : Type*} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V]

def subrepresentationSurjectiveComp (ρ : Representation k H V)
    (f : G→*H) (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f)≃o Subrepresentation ρ where
  toFun S := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule := by
      intro h v hv
      obtain ⟨g,rfl⟩ := hf h
      exact S.apply_mem_toSubmodule g hv }
  invFun S := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule := fun g _ hv=>S.apply_mem_toSubmodule (f g) hv }
  left_inv S := by cases S; rfl
  right_inv S := by cases S; rfl
  map_rel_iff' := Iff.rfl

theorem representation_irreducible_comp (ρ : Representation k H V)
    (f : G→*H) (hf : Function.Surjective f) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (ρ.comp f) :=
  (subrepresentationSurjectiveComp ρ f hf).isSimpleOrder_iff.mpr inferInstance

def representationClassCharacter [FiniteDimensional k V] (ρ : Representation k G V) :
    ConjClasses G→k :=
  Quotient.lift ρ.character (fun x y h=>by
    obtain ⟨g,rfl⟩ := isConj_iff.mp h
    exact (ρ.char_conj x g).symm)

@[simp] theorem representationClassCharacter_mk [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    representationClassCharacter ρ (ConjClasses.mk g)=ρ.character g := rfl

section Finite
variable [Fintype G] [Invertible (Nat.card G:k)]
    [FiniteDimensional k V]

def characterClassPairing (ρ : Representation k G V) : (ConjClasses G→k)→ₗ[k]k where
  toFun a := (Nat.card G:k)⁻¹*∑g,a (ConjClasses.mk g)*ρ.character g⁻¹
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib,mul_add]
  map_smul' c a := by simp [mul_assoc,mul_left_comm,Finset.mul_sum]

theorem irreducible_equiv_of_character_eq [IsAlgClosed k]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hchar : ρ.character=σ.character) : Nonempty (ρ.Equiv σ) := by
  classical
  by_contra hn
  have hcross := Representation.char_orthonormal σ ρ
  have hself := Representation.char_orthonormal ρ ρ
  rw [←hchar,if_neg hn] at hcross
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hself
  exact one_ne_zero (hself.symm.trans hcross)

theorem irreducible_character_family_card_le [IsAlgClosed k]
    {ι : Type*} [Fintype ι] (W : ι→Type*) [∀i,AddCommGroup (W i)]
    [∀i,Module k (W i)] [∀i,FiniteDimensional k (W i)]
    (ρ : ∀i,Representation k G (W i)) [∀i,Representation.IsIrreducible (ρ i)]
    (hinj : Function.Injective (fun i=>(ρ i).character)) :
    Fintype.card ι≤Nat.card (ConjClasses G) := by
  classical
  letI := Fintype.ofFinite (ConjClasses G)
  have hpair (i j : ι) : characterClassPairing (ρ j) (representationClassCharacter (ρ i))=
      if i=j then 1 else 0 := by
    change (Nat.card G:k)⁻¹*∑g,(ρ i).character g*(ρ j).character g⁻¹=_
    rw [Representation.char_orthonormal]
    by_cases h:i=j
    · subst j
      simp only [ite_true]
      exact if_pos ⟨Representation.Equiv.refl (ρ i)⟩
    · have hn : ¬Nonempty ((ρ j).Equiv (ρ i)) := by
        rintro ⟨e⟩
        exact h (hinj (Representation.char_iso e).symm)
      simp [h,hn]
  let F : (ι→k)→ₗ[k](ConjClasses G→k) := {
    toFun a := ∑i,a i • representationClassCharacter (ρ i)
    map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
    map_smul' c a := by simp [smul_smul,Finset.smul_sum] }
  have heval (a : ι→k) (j : ι) : characterClassPairing (ρ j) (F a)=a j := by
    change characterClassPairing (ρ j) (∑i,a i • representationClassCharacter (ρ i))=_
    simp [map_sum,map_smul,hpair]
  have hF : Function.Injective F := by
    intro a b h
    funext j
    exact (heval a j).symm.trans ((congrArg (characterClassPairing (ρ j)) h).trans (heval b j))
  have hd := F.finrank_le_finrank_of_injective hF
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Nat.nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hd

end Finite
end SymmetricSubgroupAsymptotics
