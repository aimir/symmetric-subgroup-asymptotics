import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Literal parameter charts INSIDE both signs of the fixed E6 upper
groups. Singleton coefficients lie in the actual sigma-fixed subfield;
paired coefficients lie in K when sigma is involutive. Each chart is an
injective group homomorphism, uniformly in all characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckRelativeRootGenerated

def fixedCoefficient (K : Type) [Field K] (sigma : K≃+*K) : Subfield K :=
  sigma.toRingHom.eqLocusField (RingHom.id K)

def coefficientInclusion (K : Type) [Field K] (sigma : K≃+*K) :
    Multiplicative (fixedCoefficient K sigma)→*Multiplicative K :=
  (fixedCoefficient K sigma).subtype.toAddMonoidHom.toMultiplicative

def singletonFixedHom (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) (j : Fin 2) :
    Multiplicative (fixedCoefficient K sigma)→*signedFixed K sigma neg :=
  ((rawSingletonHom K neg j).comp (coefficientInclusion K sigma)).codRestrict _
    (fun a=>⟨rawSimple_mem_signed K neg (CFSGTwistedE6FixedA2.node j) _,
      rawSingleton_fixed K sigma neg j _ a.toAdd.property⟩)

theorem singletonFixedHom_val (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool)
    (j : Fin 2) (a : Multiplicative (fixedCoefficient K sigma)) :
    (singletonFixedHom K sigma neg j a).val=
      rawSingletonHom K neg j (Multiplicative.ofAdd (a.toAdd : K)) := rfl

theorem singletonFixedHom_injective (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (j : Fin 2) : Function.Injective (singletonFixedHom K sigma neg j) := by
  intro a b he
  have hh := rawSingleton_injective K neg j
    (congrArg (fun z : signedFixed K sigma neg=>z.val) he)
  have hv := congrArg (fun t : Multiplicative K=>t.toAdd) hh
  change a.toAdd=b.toAdd
  exact Subtype.ext hv

def pairedFixedHom (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2) :
    Multiplicative K→*signedFixed K sigma neg :=
  (rawPairedHom K sigma neg j).codRestrict _
    (fun a=>⟨rawPaired_mem_signed K sigma neg j a,rawPaired_fixed K sigma hsigma neg j a⟩)

theorem pairedFixedHom_val (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2) (a : Multiplicative K) :
    (pairedFixedHom K sigma hsigma neg j a).val=rawPairedHom K sigma neg j a := rfl

theorem pairedFixedHom_injective (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2) :
    Function.Injective (pairedFixedHom K sigma hsigma neg j) := by
  intro a b he
  exact rawPaired_injective K sigma neg j
    (congrArg (fun z : signedFixed K sigma neg=>z.val) he)

theorem singletonFixedHom_range_card (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (j : Fin 2) :
    Nat.card (singletonFixedHom K sigma neg j).range=Nat.card (fixedCoefficient K sigma) := by
  calc
    _=Nat.card (Multiplicative (fixedCoefficient K sigma)) :=
      (Nat.card_congr (MonoidHom.ofInjective (singletonFixedHom_injective K sigma neg j)).toEquiv).symm
    _=_ := Nat.card_congr Multiplicative.toAdd

theorem pairedFixedHom_range_card (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2) :
    Nat.card (pairedFixedHom K sigma hsigma neg j).range=Nat.card K := by
  calc
    _=Nat.card (Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective (pairedFixedHom_injective K sigma hsigma neg j)).toEquiv).symm
    _=_ := Nat.card_congr Multiplicative.toAdd

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedSimpleParameters
