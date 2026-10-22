import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMovingSpan
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A derived-transfer criterion for an actual vector quotient of a
radical. Central kernel and commutator-difference witnesses are explicit
hypotheses of this GENERIC lemma; actual unitary witnesses must be built
separately. Scalar multiples are handled by rescaling the vector inside
(g-1)v, not by assuming the abelianization is a vector space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGMatrixMovingSpan
variable {K I G R H : Type*} [Field K] [Fintype I] [DecidableEq I]
variable [Group G] [Group R] [Group H]

theorem image_le_commutator_of_difference_span
    (rho : G →* (Matrix I I K)ˣ) (hspan : movingSpan rho = ⊤)
    (incl : R →* H) (nu : R →* Multiplicative (I → K))
    (hnu : Function.Surjective nu)
    (hker : ∀ r : R, nu r = 1 → incl r ∈ commutator H)
    (hmove : ∀ g : G, ∀ v : I → K, ∃ r : R,
      incl r ∈ commutator H ∧
        nu r = Multiplicative.ofAdd ((rho g : Matrix I I K) *ᵥ v - v))
    (r : R) : incl r ∈ commutator H := by
  let phi : R →* Abelianization H := (Abelianization.of : H →* Abelianization H).comp incl
  have hk : nu.ker ≤ phi.ker := by
    intro x hx
    change (Abelianization.of : H →* Abelianization H) (incl x) = 1
    change incl x ∈ (Abelianization.of : H →* Abelianization H).ker
    rw [Abelianization.ker_of]
    exact hker x hx
  let e : R ⧸ nu.ker ≃* Multiplicative (I → K) :=
    QuotientGroup.liftEquiv nu.ker hnu rfl
  let psi : Multiplicative (I → K) →* Abelianization H :=
    (QuotientGroup.lift nu.ker phi hk).comp e.symm.toMonoidHom
  have he (x : R) : e (QuotientGroup.mk x) = nu x := rfl
  have hp (x : R) : psi (nu x) = phi x := by
    change QuotientGroup.lift nu.ker phi hk (e.symm (nu x)) = phi x
    rw [← he x, e.symm_apply_apply]
    rfl
  have hp1 (x : R) (hx : incl x ∈ commutator H) : psi (nu x) = 1 := by
    rw [hp]
    change incl x ∈ (Abelianization.of : H →* Abelianization H).ker
    rwa [Abelianization.ker_of]
  have hall (v : I → K) (hv : v ∈ movingSpan rho) :
      ∀ a : K, psi (Multiplicative.ofAdd (a • v)) = 1 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, w, rfl⟩ := hv
      intro a
      obtain ⟨x, hx, hv⟩ := hmove g (a • w)
      have hh := hp1 x hx
      rw [hv] at hh
      simpa only [Matrix.mulVec_smul, smul_sub] using hh
    | zero =>
      intro a
      simp
    | add x y _ _ ihx ihy =>
      intro a
      rw [smul_add, ofAdd_add, map_mul, ihx a, ihy a, one_mul]
    | smul a v _ ih =>
      intro b
      rw [smul_smul]
      exact ih (b * a)
  have hz : psi (nu r) = 1 := by
    have hv : (nu r).toAdd ∈ movingSpan rho := by rw [hspan]; trivial
    simpa only [one_smul, ofAdd_toAdd] using hall (nu r).toAdd hv 1
  rw [hp] at hz
  change incl r ∈ (Abelianization.of : H →* Abelianization H).ker at hz
  rwa [Abelianization.ker_of] at hz

end SymmetricSubgroupAsymptotics.CFSGMatrixMovingSpan
