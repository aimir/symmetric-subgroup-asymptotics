import SymmetricSubgroupAsymptotics.BinaryRegularTranslationFixedVectors
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A regular binary translation basis and ONE actual linear map taking
the nonzero translation-fixed vector to a basis vector force generation.
Irreducibility is proved from these displayed actions, never assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularTranslationGeneration
open Module
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def restrictAction (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) : G →* (W ≃ₗ[K] W) where
  toFun g := {
    toFun x := ⟨ρ g x.val,hW g x.val x.property⟩
    invFun x := ⟨(ρ g).symm x.val,by
      have h := hW g⁻¹ x.val x.property
      rw [map_inv] at h
      exact h⟩
    left_inv x := Subtype.ext ((ρ g).symm_apply_apply x.val)
    right_inv x := Subtype.ext ((ρ g).apply_symm_apply x.val)
    map_add' x y := Subtype.ext ((ρ g).map_add x.val y.val)
    map_smul' c x := Subtype.ext ((ρ g).map_smul c x.val) }
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ρ 1 x.val=x.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ρ (g*h) x.val=ρ g (ρ h x.val)
    rw [map_mul]
    rfl

theorem restrictAction_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) (g : G) (x : W) :
    (restrictAction ρ W hW g x).val=ρ g x.val := rfl

theorem exists_nonzero_fixed_in [Finite K] [Module.Finite K V]
    (hK : Nat.card K=2) (hG : IsPGroup 2 G) (ρ : G →* (V ≃ₗ[K] V))
    (W : Submodule K V) (hWne : W≠⊥) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ v : V, v∈W ∧ v≠0 ∧ ∀ g : G, ρ g v=v := by
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  obtain ⟨v,hv,hfix⟩ := BinaryPGroupLinearFixedVector.exists_nonzero_fixed
    hK hG (restrictAction ρ W hW)
  refine ⟨v.val,v.property,?_,?_⟩
  · intro he
    exact hv (Subtype.ext he)
  · intro g
    exact congrArg (fun x : W => x.val) (hfix g)

theorem eq_bot_or_eq_top [Finite K] [Module.Finite K V] {A : Type*} [AddGroup A]
    (hK : Nat.card K=2) (hA : IsPGroup 2 (Multiplicative A))
    (b : Basis A K V) (ρ : Multiplicative A →* (V ≃ₗ[K] V))
    (htranslate : ∀ a t : A, ρ (Multiplicative.ofAdd a) (b t)=b (a+t))
    (η : V) (hη : η≠0) (hηfix : ∀ a : A, ρ (Multiplicative.ofAdd a) η=η)
    (s : V →ₗ[K] V) (hs : s η=b 0)
    (W : Submodule K V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W)
    (hsW : ∀ x ∈ W, s x ∈ W) : W=⊥ ∨ W=⊤ := by
  by_cases hWne : W=⊥
  · exact Or.inl hWne
  right
  obtain ⟨v,hv,hv0,hvfix⟩ := exists_nonzero_fixed_in hK hA ρ W hWne hW
  have he : v=η := BinaryRegularTranslationFixedVectors.fixed_nonzero_unique
    b ρ htranslate hK v η hv0 hη (fun a => hvfix (Multiplicative.ofAdd a)) hηfix
  have hηW : η∈W := he ▸ hv
  have hzero : b 0∈W := hs ▸ hsW η hηW
  have hb (a : A) : b a∈W := by
    have h := hW (Multiplicative.ofAdd a) (b 0) hzero
    rwa [htranslate,add_zero] at h
  have hspan : Submodule.span K (Set.range b) ≤ W :=
    Submodule.span_le.mpr (by rintro x ⟨a,rfl⟩; exact hb a)
  rw [b.span_eq] at hspan
  exact top_unique hspan

end SymmetricSubgroupAsymptotics.BinaryRegularTranslationGeneration
