import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
import SymmetricSubgroupAsymptotics.CFSGEmbeddedLinearRayScalar
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Field.ZMod

/-! Every actual faithful linear group on a nine-element F3 plane has
at most ten classes. Its literal action on the four projective points
has a scalar kernel of cardinal at most two and a faithful four-point
image. No exceptional PGL isomorphism or group catalogue is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.FiniteLinearPlaneClassBound

local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev Scalar := ZMod 3

variable {V H : Type*} [AddCommGroup V] [Module Scalar V]
    [Group H] (ρ : H →* (V ≃ₗ[Scalar] V))

def pointHom : H →* Equiv.Perm (Projectivization Scalar V) :=
  (MulAction.toPermHom (V ≃ₗ[Scalar] V) (Projectivization Scalar V)).comp ρ

theorem projective_card [Finite V] (hV : Nat.card V = 9) :
    Nat.card (Projectivization Scalar V) = 4 := by
  have hc := Projectivization.card Scalar V
  have hK : Nat.card Scalar = 3 := Nat.card_zmod 3
  rw [hV, hK] at hc
  omega

private theorem scalar_of_pointHom_eq_one
    (e : V ≃ₗ[Scalar] V)
    (he : MulAction.toPermHom (V ≃ₗ[Scalar] V) (Projectivization Scalar V) e = 1) :
    ∃ c : Scalar, ∀ v : V, e v = c • v := by
  apply CFSGEmbeddedLinearRayScalar.exists_scalar LinearMap.id e.toLinearMap
    Function.injective_id
  intro v
  by_cases hv : v = 0
  · exact ⟨0, by simp only [hv, map_zero, smul_zero]⟩
  · have hp := congrArg (fun f : Equiv.Perm (Projectivization Scalar V) =>
      f (Projectivization.mk Scalar v hv)) he
    change e • Projectivization.mk Scalar v hv = Projectivization.mk Scalar v hv at hp
    rw [Projectivization.smul_mk] at hp
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff Scalar _ _ _ _).mp hp
    exact ⟨c.val, hc.symm⟩

theorem pointHom_kernel_card_le_two [Finite V] (hV : Nat.card V = 9)
    (hρ : Function.Injective ρ) : Nat.card (pointHom ρ).ker ≤ 2 := by
  letI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hscalar (g : (pointHom ρ).ker) :
      ∃ c : Scalar, c ≠ 0 ∧ ∀ v : V, ρ g.val v = c • v := by
    have hg : MulAction.toPermHom (V ≃ₗ[Scalar] V)
        (Projectivization Scalar V) (ρ g.val) = 1 := g.property
    obtain ⟨c, hc⟩ := scalar_of_pointHom_eq_one (ρ g.val) hg
    refine ⟨c, ?_, hc⟩
    intro hc0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have he : ρ g.val v = 0 := by rw [hc, hc0, zero_smul]
    exact hv ((ρ g.val).injective (he.trans (map_zero (ρ g.val)).symm))
  choose c hc0 hc using hscalar
  let f : (pointHom ρ).ker → Scalarˣ := fun g => Units.mk0 (c g) (hc0 g)
  have hf : Function.Injective f := by
    intro g h he
    have hec : c g = c h := congrArg Units.val he
    apply Subtype.ext
    apply hρ
    apply LinearEquiv.ext
    intro v
    rw [hc g v, hc h v, hec]
  have hK : Nat.card Scalarˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact (Nat.card_le_card_of_injective f hf).trans_eq hK

theorem class_card_le_ten [Finite V] [Finite H] (hV : Nat.card V = 9)
    (hρ : Function.Injective ρ) : Nat.card (ConjClasses H) ≤ 10 := by
  have hs := conjugacyClass_card_le_kernel_mul_range (pointHom ρ)
  have hk : Nat.card (ConjClasses (pointHom ρ).ker) ≤ 2 :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk (pointHom ρ).ker _)
      ConjClasses.mk_surjective).trans (pointHom_kernel_card_le_two ρ hV hρ)
  let e : Projectivization Scalar V ≃ Fin 4 := Finite.equivFinOfCardEq (projective_card hV)
  let a := e.permCongrHom.subgroupMap (pointHom ρ).range
  have hi : Nat.card (ConjClasses (pointHom ρ).range) ≤ 5 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
      (ConjClasses.map_surjective a.symm.surjective)).trans
        (FourPointPermutationClassBound.subgroup_class_card_le_five _)
  exact hs.trans (by simpa only [show 2*5=10 by decide] using Nat.mul_le_mul hk hi)

end SymmetricSubgroupAsymptotics.FiniteLinearPlaneClassBound
