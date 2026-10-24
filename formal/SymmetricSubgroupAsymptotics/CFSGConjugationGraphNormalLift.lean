import SymmetricSubgroupAsymptotics.CFSGConjugationActionGraph
import Mathlib.Algebra.Group.Subgroup.Ker

/-! A normal subgroup in the literal conjugation graph. Faithfulness is
required only for the displayed parameter action and its actual embedding;
surjectivity onto an abstract automorphism group is never assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGConjugationGraphNormalLift
open CFSGConjugationActionGraph

variable {B L G : Type*} [Group B] [Group L] [Group G]
    (ρ : L →* MulAut B) (ψ : B →* G)

def second : intertwiningPairs ρ ψ →* G :=
  (MonoidHom.snd L G).comp (intertwiningPairs ρ ψ).subtype

theorem second_injective (hρ : Function.Injective ρ) (hψ : Function.Injective ψ) :
    Function.Injective (second ρ ψ) := by
  intro a b hab
  have hsecond : a.val.2 = b.val.2 := hab
  have hfirst : a.val.1 = b.val.1 := by
    apply hρ
    apply MulEquiv.ext
    intro x
    apply hψ
    apply mul_right_cancel (b := b.val.2)
    calc
      ψ (ρ a.val.1 x) * b.val.2 = b.val.2 * ψ x := by
        rw [← hsecond]
        exact (a.property x).symm
      _ = ψ (ρ b.val.1 x) * b.val.2 := b.property x
  exact Subtype.ext (Prod.ext hfirst hsecond)

def normalLift (N : Subgroup G) : Subgroup (intertwiningPairs ρ ψ) :=
  N.comap (second ρ ψ)

instance normalLift_normal (N : Subgroup G) [N.Normal] : (normalLift ρ ψ N).Normal :=
  inferInstanceAs (N.comap (second ρ ψ)).Normal

/-- The actual radical embeds with identity action on its central
parameter chart. No complement or lift of all abstract automorphisms is used. -/
def normalLiftHom (N : Subgroup G)
    (hcentral : ∀ n : N, ∀ b : B, (n : G) * ψ b = ψ b * n) :
    N →* normalLift ρ ψ N where
  toFun n := ⟨⟨(1, (n : G)), by
    intro b
    change (n : G) * ψ b = ψ (ρ 1 b) * n
    simpa only [map_one, MulAut.one_apply] using hcentral n b⟩, n.property⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp) rfl
  map_mul' n m := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp) rfl

/-- The graph's normal radical is exactly the original subgroup, even if
the first projection has only a proper subgroup as its range. -/
def normalLiftEquiv (N : Subgroup G)
    (hρ : Function.Injective ρ) (hψ : Function.Injective ψ)
    (hcentral : ∀ n : N, ∀ b : B, (n : G) * ψ b = ψ b * n) :
    N ≃* normalLift ρ ψ N :=
  MulEquiv.ofBijective (normalLiftHom ρ ψ N hcentral) ⟨by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun a : normalLift ρ ψ N => second ρ ψ a.val) h, by
    intro a
    refine ⟨⟨second ρ ψ a.val, a.property⟩, ?_⟩
    apply Subtype.ext
    apply second_injective ρ ψ hρ hψ
    rfl⟩

theorem normalLiftEquiv_second (N : Subgroup G)
    (hρ : Function.Injective ρ) (hψ : Function.Injective ψ)
    (hcentral : ∀ n : N, ∀ b : B, (n : G) * ψ b = ψ b * n) (n : N) :
    second ρ ψ (normalLiftEquiv ρ ψ N hρ hψ hcentral n).val = (n : G) := rfl

end SymmetricSubgroupAsymptotics.CFSGConjugationGraphNormalLift
