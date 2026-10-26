import SymmetricSubgroupAsymptotics.BlockKernelSignCoordinates
import SymmetricSubgroupAsymptotics.BinaryBlockKernelAbelian
import SymmetricSubgroupAsymptotics.AbelianExtensionUnsignedPermutationClassBound

/-! Literal binary fibre signs give faithful UNSIGNED coordinates for the
original block kernel. The acting quotient is the original group's actual
top quotient. No independent fibre permutations, splitting, transitivity,
primitivity or full-base hypothesis is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryBlockUnsignedKernelCoordinates
open OriginalBlockClassBound
open OriginalBlockSignCoordinates (coordinateSign coordinateSign_conjugation)

/-- On a set of at most two points, parity detects the whole permutation. -/
theorem permutationBinarySign_injective {Y : Type} [Fintype Y]
    (hY : Nat.card Y≤2) : Function.Injective (permutationBinarySign Y) := by
  apply (injective_iff_map_eq_one (permutationBinarySign Y)).mpr
  intro s hs
  by_contra hne
  have hl := Equiv.Perm.two_le_card_support_of_ne_one hne
  have hu := s.support.card_le_univ
  have hc : s.support.card=2 := by
    rw [←Nat.card_eq_fintype_card] at hu
    omega
  have hswap := Equiv.Perm.card_support_eq_two.mp hc
  have hp := (permutationBinarySign_eq_one Y s).mp hs
  have hn := hswap.sign_eq
  rw [hp] at hn
  norm_num at hn

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite Ω] (b : Ω→X)
    (hb : ∀ (a : A) (ω : Ω),b (a•ω)=a•b ω)

local instance fibreFintype (x : X) : Fintype (originalBlockFibre b x) :=
  Fintype.ofFinite _

/-- All actual fibre characters are recorded simultaneously. -/
def coordinates : Kernel (A:=A) (X:=X) →* Multiplicative (X→ZMod 2) where
  toFun u := Multiplicative.ofAdd (fun x => (coordinateSign b hb x u).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_one (coordinateSign b hb x))
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_mul (coordinateSign b hb x) u v)

/-- Kernel correlations are retained: only its existing coordinates are used. -/
theorem coordinates_injective [FaithfulSMul A Ω]
    (hsmall : ∀x,Nat.card (originalBlockFibre b x)≤2) :
    Function.Injective (coordinates b hb) := by
  intro u v he
  apply OriginalBlockClassBound.coordinates_injective b hb
  funext x
  apply permutationBinarySign_injective (hsmall x)
  apply Multiplicative.toAdd.injective
  exact congrFun (congrArg Multiplicative.toAdd he) x

/-- Ambient conjugation permutes the same original coordinates with no sign
scalar. The assertion uses the full correlated kernel. -/
theorem coordinates_conjugation (a : A) (u : Kernel (A:=A) (X:=X)) :
    (coordinates b hb (MulAut.conjNormal a u)).toAdd=
      fun x => (coordinates b hb u).toAdd (a⁻¹•x) := by
  funext x
  change (coordinateSign b hb x (MulAut.conjNormal a u)).toAdd=
    (coordinateSign b hb (a⁻¹•x) u).toAdd
  apply congrArg Multiplicative.toAdd
  simpa only [smul_inv_smul] using
    coordinateSign_conjugation b hb a (a⁻¹•x) u

/-- The actual block action factors through its own kernel, without replacing
its image by a full symmetric group. -/
def quotientHom : A ⧸ Kernel (A:=A) (X:=X) →* Equiv.Perm X :=
  QuotientGroup.lift (Kernel (A:=A) (X:=X))
    (topMap (A:=A) (X:=X)) le_rfl

def quotientAction : MulAction (A ⧸ Kernel (A:=A) (X:=X)) X :=
  MulAction.compHom X (quotientHom (A:=A) (X:=X))

/-- Quotient conjugation and the actual quotient point action intertwine on
these faithful unsigned coordinates. -/
theorem quotient_intertwine [FaithfulSMul A Ω]
    (hsmall : ∀x,Nat.card (originalBlockFibre b x)≤2) :
    letI : IsMulCommutative (Kernel (A:=A) (X:=X)) :=
      BinaryBlockKernelAbelian.kernel_isMulCommutative b hb hsmall
    letI : MulAction (A ⧸ Kernel (A:=A) (X:=X)) X :=
      quotientAction (A:=A) (X:=X)
    ∀ (q : A ⧸ Kernel (A:=A) (X:=X)) (u : Kernel (A:=A) (X:=X)),
      (coordinates b hb (AbelianExtensionConjugation.quotientConjugation _ q u)).toAdd=
        permutationFunctionRepresentation (ZMod 2) (A ⧸ Kernel (A:=A) (X:=X)) X q
          (coordinates b hb u).toAdd := by
  letI : IsMulCommutative (Kernel (A:=A) (X:=X)) :=
    BinaryBlockKernelAbelian.kernel_isMulCommutative b hb hsmall
  letI : MulAction (A ⧸ Kernel (A:=A) (X:=X)) X :=
    quotientAction (A:=A) (X:=X)
  intro q u
  induction q using QuotientGroup.induction_on with
  | H a =>
    change (coordinates b hb (MulAut.conjNormal a u)).toAdd=
      fun x => (coordinates b hb u).toAdd (a⁻¹•x)
    exact coordinates_conjugation b hb a u

end SymmetricSubgroupAsymptotics.BinaryBlockUnsignedKernelCoordinates
