import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Group.Equiv.Basic

/-! Intrinsic coordinate products intertwine any permutation of the
factor labels and literal factor isomorphisms, as soon as their SINGLE
factor inclusions intertwine. Fixedness is then a joint coordinate
condition, with no scalar-chart choices or orbit-length assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFinitePermutedGroupCoordinates
variable {I H : Type*} (G : I → Type*) [∀ i,Group (G i)] [Group H]
local instance : DecidableEq I := Classical.decEq I
variable (p : Equiv.Perm I) (T : ∀ i,G i ≃* G (p i))

def permutedPiEquiv : MulAut (∀ i,G i) where
  toEquiv := p.piCongr (fun i => (T i).toEquiv)
  map_mul' x y := by
    funext j
    obtain ⟨i,rfl⟩ := p.surjective j
    change (p.piCongr (fun i => (T i).toEquiv)) (x*y) (p i) =
      (p.piCongr (fun i => (T i).toEquiv)) x (p i) *
        (p.piCongr (fun i => (T i).toEquiv)) y (p i)
    rw [Equiv.piCongr_apply_apply,Equiv.piCongr_apply_apply,Equiv.piCongr_apply_apply]
    exact (T i).map_mul (x i) (y i)

theorem permutedPiEquiv_apply (c : ∀ i,G i) (i : I) :
    permutedPiEquiv G p T c (p i) = T i (c i) :=
  Equiv.piCongr_apply_apply p (fun i => (T i).toEquiv) c i

theorem permutedPiEquiv_mulSingle [DecidableEq I] (i : I) (x : G i) :
    permutedPiEquiv G p T (Pi.mulSingle i x) = Pi.mulSingle (p i) (T i x) := by
  funext j
  obtain ⟨k,rfl⟩ := p.surjective j
  rw [permutedPiEquiv_apply]
  by_cases hki : k=i
  · subst k
    simp
  · simp [hki,p.injective.ne hki]

theorem permutedPiEquiv_fixed_iff (c : ∀ i,G i) :
    permutedPiEquiv G p T c = c ↔ ∀ i,T i (c i) = c (p i) := by
  constructor
  · intro h i
    have hi := congrFun h (p i)
    exact (permutedPiEquiv_apply G p T c i).symm.trans hi
  · intro h
    funext j
    obtain ⟨i,rfl⟩ := p.surjective j
    exact (permutedPiEquiv_apply G p T c i).trans (h i)

variable [Finite I] (E : (∀ i,G i) ≃* H) (F : MulAut H)
variable (hsingle : ∀ i (x : G i),
    F (E (Pi.mulSingle i x)) = E (Pi.mulSingle (p i) (T i x)))
include hsingle

theorem product_intertwines (c : ∀ i,G i) :
    F (E c) = E (permutedPiEquiv G p T c) := by
  classical
  have he : F.toMonoidHom.comp E.toMonoidHom =
      E.toMonoidHom.comp (permutedPiEquiv G p T).toMonoidHom := by
    apply MonoidHom.pi_ext
    intro i x
    change F (E (Pi.mulSingle i x)) = E (permutedPiEquiv G p T (Pi.mulSingle i x))
    rw [permutedPiEquiv_mulSingle]
    exact hsingle i x
  exact DFunLike.congr_fun he c

theorem product_fixed_iff (c : ∀ i,G i) :
    F (E c) = E c ↔ ∀ i,T i (c i) = c (p i) := by
  rw [product_intertwines G p T E F hsingle]
  exact E.injective.eq_iff.trans (permutedPiEquiv_fixed_iff G p T c)

end SymmetricSubgroupAsymptotics.CFSGFinitePermutedGroupCoordinates
