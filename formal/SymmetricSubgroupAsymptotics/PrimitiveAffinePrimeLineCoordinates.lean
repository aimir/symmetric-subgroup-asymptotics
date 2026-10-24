import SymmetricSubgroupAsymptotics.ScalarAffineLineGroup
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Aut

/-! Prime-degree affine profiles embed in the literal scalar affine line.
The regular subgroup is identified with the additive prime field by its
actual prime cardinality. Conjugation is transported through that same
identification; no abstract affine-component recognition is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeLineCoordinates
open ScalarAffineLineGroup

variable (p : ℕ) [Fact p.Prime]

/-- Every automorphism of the additive prime field is scalar multiplication. -/
def primeAutScalar : MulAut (Multiplicative (ZMod p)) ≃* (ZMod p)ˣ :=
  (MulAutMultiplicative (ZMod p)).trans (ZMod.AddAutEquivUnits p)

theorem primeAutScalar_action (f : MulAut (Multiplicative (ZMod p))) :
    scalarAction (ZMod p) (primeAutScalar p f) = f := by
  apply (MulAutMultiplicative (ZMod p)).injective
  exact (ZMod.AddAutEquivUnits p).symm_apply_apply
    (MulAutMultiplicative (ZMod p) f)

section Semidirect
variable {A H : Type} [Group A] [Group H]
    (e : A ≃* Multiplicative (ZMod p)) (phi : H →* MulAut A)

def complementScalar : H →* (ZMod p)ˣ :=
  (primeAutScalar p).toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp phi)

theorem complementScalar_intertwine (h : H) :
    e.toMonoidHom.comp (phi h).toMonoidHom =
      (scalarAction (ZMod p) (complementScalar p e phi h)).toMonoidHom.comp
        e.toMonoidHom := by
  change e.toMonoidHom.comp (phi h).toMonoidHom =
    (scalarAction (ZMod p) (primeAutScalar p (MulAut.congr e (phi h)))).toMonoidHom.comp
      e.toMonoidHom
  rw [primeAutScalar_action]
  apply MonoidHom.ext
  intro a
  change e (phi h a) = e (phi h (e.symm (e a)))
  rw [e.symm_apply_apply]

def semidirectCoordinates : A ⋊[phi] H →* Line (ZMod p) :=
  SemidirectProduct.map e.toMonoidHom (complementScalar p e phi)
    (complementScalar_intertwine p e phi)

theorem semidirectCoordinates_injective (hphi : Function.Injective phi) :
    Function.Injective (semidirectCoordinates p e phi) := by
  intro a b hab
  apply SemidirectProduct.ext
  · exact e.injective (congrArg (fun z : Line (ZMod p) => z.left) hab)
  · apply hphi
    apply (MulAut.congr e).injective
    apply (primeAutScalar p).injective
    exact congrArg (fun z : Line (ZMod p) => z.right) hab
end Semidirect

section Profile
variable {G Ω : Type} [Group G] [Finite G] [Finite Ω]
    [MulAction G Ω] (P : PrimitiveAffineProfile G Ω)
    (x : Ω) (hdegree : Nat.card Ω = p)

/-- This is a chart of the actual translation subgroup, not a replacement
regular subgroup of an abstract permutation group. -/
def translationEquiv : P.V ≃* Multiplicative (ZMod p) := by
  have hc : Nat.card P.V = p := (P.card_eq x).trans hdegree
  letI : IsCyclic P.V := isCyclic_of_prime_card hc
  have e := (zmodCyclicMulEquiv (G := P.V) inferInstance).symm
  rw [hc] at e
  exact e

def coordinates : G →* Line (ZMod p) :=
  (semidirectCoordinates p (translationEquiv p P x hdegree)
    (P.complementAction x)).comp (P.semidirectEquiv x).symm.toMonoidHom

include hdegree in
theorem coordinates_injective [FaithfulSMul G Ω] :
    Function.Injective (coordinates p P x hdegree) :=
  (semidirectCoordinates_injective p (translationEquiv p P x hdegree)
    (P.complementAction x) (P.complementAction_injective x)).comp
      (P.semidirectEquiv x).symm.injective

include P x hdegree in
/-- A finite faithful affine profile of prime degree has genuine jointly
faithful scalar-affine coordinates, with no ordinary-generator premise. -/
theorem exists_injective_coordinates [FaithfulSMul G Ω] :
    ∃ f : G →* Line (ZMod p), Function.Injective f :=
  ⟨coordinates p P x hdegree,coordinates_injective p P x hdegree⟩
end Profile
end SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeLineCoordinates
