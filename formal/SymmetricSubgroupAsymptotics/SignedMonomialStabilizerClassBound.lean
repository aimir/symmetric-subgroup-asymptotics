import SymmetricSubgroupAsymptotics.SignedMonomialFixedCoordinateCode
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.Data.Finite.Perm

/-! A fixed monomial vector leaves only units and permutations on its
zero coordinates in the kernel of the actual support-permutation map.
The class bound uses that kernel and that map's actual range. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SignedMonomialStabilizerClassBound
open SignedMonomialFixedCoordinateCode

variable {G I K : Type*} [Group G] [Field K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))

def fixedSubgroup (v : I → K) : Subgroup G :=
  letI : MulAction G (I → K) := MulAction.compHom _ ρ
  MulAction.stabilizer G v

def supportPermHom (v : I → K) :
    fixedSubgroup ρ v →* Equiv.Perm {i : I // v i≠0} where
  toFun g := (t g.val).subtypePerm
    (fixed_support_iff ρ t a hformula g.val v g.property)
  map_one' := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun s : Equiv.Perm I => s i.val) (map_one t)
  map_mul' g h := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun s : Equiv.Perm I => s i.val) (map_mul t g.val h.val)

include hformula in
theorem class_card_le_zero_coefficients_mul_support_budget
    [Finite G] [Finite I] [Finite K] (hρ : Function.Injective ρ)
    (v : I → K) (d : ℕ)
    (hsupport : ∀ L : Subgroup (Equiv.Perm {i : I // v i≠0}),
      Nat.card (ConjClasses L)≤d) :
    Nat.card (ConjClasses (fixedSubgroup ρ v))≤
      Nat.card Kˣ ^ Nat.card {i : I // v i=0} *
        (Nat.card {i : I // v i=0}).factorial*d := by
  let f := supportPermHom ρ t a hformula v
  let Z := {i : I // v i=0}
  have hzero (g : f.ker) : ∀ i,v (t g.val.val i)=0 ↔ v i=0 := by
    intro i
    simpa only [not_not] using not_congr
      (fixed_support_iff ρ t a hformula g.val.val v g.val.property i)
  let code : f.ker → (Z → Kˣ) × Equiv.Perm Z := fun g =>
    (fun i => a g.val.val i.val,(t g.val.val).subtypePerm (hzero g))
  have hsupportFixed (g : f.ker) (i : I) (hi : v i≠0) : t g.val.val i=i := by
    have h := congrArg (fun s : Equiv.Perm {i : I // v i≠0} => (s ⟨i,hi⟩).val)
      (show f g.val=1 from g.property)
    exact h
  have hcode : Function.Injective code := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    apply fixed_element_eq_of_zero_coefficients ρ t a hformula hρ v
      g.val.val h.val.val g.val.property h.val.property
    · apply Equiv.ext
      intro i
      by_cases hi : v i=0
      · exact congrArg (fun s : Equiv.Perm Z => (s ⟨i,hi⟩).val) (congrArg Prod.snd he)
      · exact (hsupportFixed g i hi).trans (hsupportFixed h i hi).symm
    · intro i hi
      exact congrFun (congrArg Prod.fst he) ⟨i,hi⟩
  have hk : Nat.card f.ker≤Nat.card Kˣ ^ Nat.card Z*(Nat.card Z).factorial := by
    have h := Nat.card_le_card_of_injective code hcode
    simpa only [Nat.card_prod,Nat.card_fun,Nat.card_perm] using h
  have hkclass : Nat.card (ConjClasses f.ker)≤
      Nat.card Kˣ ^ Nat.card Z*(Nat.card Z).factorial :=
    (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans hk
  exact (conjugacyClass_card_le_kernel_mul_range f).trans
    (Nat.mul_le_mul hkclass (hsupport f.range))

end SymmetricSubgroupAsymptotics.SignedMonomialStabilizerClassBound
