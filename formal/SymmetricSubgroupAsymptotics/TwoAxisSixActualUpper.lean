import SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators
import SymmetricSubgroupAsymptotics.SmallBinaryTopProperRelativeHead
import SymmetricSubgroupAsymptotics.OddDerivedKernelProperRelativeHead
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.TwoAxisSixActualUpper
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open SemidirectProduct
open SixPointTernaryAxesNormalGenerators (Model Local literalAction translation reflection)
abbrev Binary := TernarySwapUpperNormalGenerators.Binary
abbrev Upper := Binary × Binary
local instance : Fintype Local := Fintype.ofEquiv
  (TernarySwapUpperNormalGenerators.Ternary × Binary) SemidirectProduct.equivProd.symm
local instance : DecidableEq Local := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩
      exact SemidirectProduct.ext hl hr
    · intro he
      exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)
def modelProjection : Model →* Upper :=
  (rightHom : Local →* Binary).prodMap (rightHom : Local →* Binary)
def inversionLift : Model := (translation^2*reflection,translation*reflection)
def swapLift : Model := (1,translation*reflection)

theorem action_injective : Function.Injective literalAction := by
  have h : ∀ g h : Model,(∀ i : Fin 6,literalAction g i=literalAction h i) → g=h := by
    decide +kernel
  exact fun _ _ he => h _ _ (fun i => congrArg (fun p : Equiv.Perm (Fin 6) => p i) he)
def canonicalEquiv : Model ≃* literalAction.range :=
  MulEquiv.ofBijective literalAction.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),literalAction.rangeRestrict_surjective⟩
variable (P : Subgroup (Equiv.Perm (Fin 6))) (hle : P≤literalAction.range)
def toModel : P →* Model := canonicalEquiv.symm.toMonoidHom.comp (Subgroup.inclusion hle)
theorem toModel_action (p : P) : literalAction (toModel P hle p)=(p : Equiv.Perm (Fin 6)) :=
  congrArg Subtype.val (canonicalEquiv.apply_symm_apply ⟨p.val,hle p.property⟩)
theorem toModel_injective : Function.Injective (toModel P hle) := by
  intro p q h
  apply Subtype.ext
  simpa only [toModel_action] using congrArg literalAction h
def projection : P →* Upper := modelProjection.comp (toModel P hle)
theorem projection_code (p : P) (g : Model) (he : literalAction g=(p : Equiv.Perm (Fin 6))) :
    projection P hle p=modelProjection g := by
  have ht : toModel P hle p=g := action_injective ((toModel_action P hle p).trans he.symm)
  change modelProjection (toModel P hle p)=modelProjection g
  rw [ht]

variable (hinv : literalAction inversionLift∈P) (hswap : literalAction swapLift∈P)
def inversionElement : P := ⟨literalAction inversionLift,hinv⟩
def swapElement : P := ⟨literalAction swapLift,hswap⟩
include hinv hswap in
theorem projection_surjective : Function.Surjective (projection P hle) := by
  have hc : ∀ c : Upper,∃ i j : Fin 2,
      modelProjection inversionLift^i.val*modelProjection swapLift^j.val=c := by decide +kernel
  intro c
  obtain ⟨i,j,hij⟩ := hc c
  refine ⟨inversionElement P hinv^i.val*swapElement P hswap^j.val,?_⟩
  rw [map_mul,map_pow,map_pow,projection_code P hle _ inversionLift rfl,
    projection_code P hle _ swapLift rfl]
  exact hij

theorem kernel_isPGroup : IsPGroup 3 (projection P hle).ker := by
  have hc : ∀ g : Model,modelProjection g=1 → g^3=1 := by decide +kernel
  intro x
  refine ⟨1,?_⟩
  apply Subtype.ext
  apply toModel_injective P hle
  change toModel P hle (x.val^3)=toModel P hle 1
  rw [map_pow,map_one]
  exact hc _ x.property

theorem kernel_commutative : IsMulCommutative (projection P hle).ker := by
  have hc : ∀ g h : Model,modelProjection g=1 → modelProjection h=1 → g*h=h*g := by
    decide +kernel
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  apply toModel_injective P hle
  change toModel P hle (x.val*y.val)=toModel P hle (y.val*x.val)
  rw [map_mul,map_mul]
  exact hc _ _ x.property y.property

include hinv in
theorem kernel_le_derived : (projection P hle).ker≤commutator P := by
  have hc : ∀ g : Model,modelProjection g=1 → g=⁅g,inversionLift⁆^2 := by decide +kernel
  intro x hx
  have he : x=⁅x,inversionElement P hinv⁆^2 := by
    apply toModel_injective P hle
    rw [map_pow,map_commutatorElement]
    have ht : toModel P hle (inversionElement P hinv)=inversionLift :=
      action_injective (toModel_action P hle _)
    rw [ht]
    exact hc _ hx
  rw [he]
  exact (commutator P).pow_mem
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top _)) 2

include hle hinv hswap in
theorem proper_head (M : Subgroup P) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  apply OddDerivedKernelProperRelativeHead.relative_head_le_one (projection P hle)
    (projection_surjective P hle hinv hswap) (kernel_commutative P hle)
    (kernel_le_derived P hle hinv) (kernel_isPGroup P hle) ?_ M hne
  intro L _ hL
  apply SmallBinaryTopProperRelativeHead.order_four (R := Upper) ?_ L hL
  norm_num [Upper,Binary,TernarySwapUpperNormalGenerators.Binary,Nat.card_prod,Nat.card_eq_fintype_card]
end SymmetricSubgroupAsymptotics.TwoAxisSixActualUpper
