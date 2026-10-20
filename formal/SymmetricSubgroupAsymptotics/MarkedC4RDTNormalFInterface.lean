import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Real.Basic

/-! LIT-RDTTheorem4.6: the unmarked bounded-factor epimorphism theorem,
with its ARBITRARY normal target subgroup F retained. This is a named
literature hypothesis, not an axiom and not a marked enumeration callback.
The source is a literal subgroup of R×P, with its actual projection kernel.
The nontrivial-target restriction suffices for the nonabelian Case-II use.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.RDTNormalFInterface

def RDTTheorem46BinaryInput : Prop :=
  ∀ k : ℕ,∃ κ₃ κ₄ : ℝ,0<κ₃ ∧ 0≤κ₄ ∧
    ∀ (s u : ℕ) (R : Fin s → Type) [∀ i,Group (R i)] [∀ i,Finite (R i)]
      (P : Fin u → Type) [∀ j,Group (P j)] [∀ j,Finite (P j)],
    (∀ i,IsPGroup 2 (R i)) → (∀ j,IsPGroup 2 (P j)) →
    (∀ i,Nat.card (R i)≤2^k) → (∀ j,Nat.card (P j)≤2^k) →
    ∀ L : Subgroup (∀ i,R i),
    (∀ i,Function.Surjective ((Pi.evalMonoidHom R i).comp L.subtype)) →
    ∀ G : Subgroup (L × (∀ j,P j)),
    Function.Surjective ((MonoidHom.snd L (∀ j,P j)).comp G.subtype) →
    ∀ (Q : Type) [Group Q] [Finite Q] [Nontrivial Q],IsPGroup 2 Q → Nat.card Q≤2^k →
    ∀ F : Subgroup Q,F.Normal → ∀ dN : ℕ,
    (∀ U : Subgroup G,U.Normal →
      U≤commutator G ⊓ ((MonoidHom.snd L (∀ j,P j)).comp G.subtype).ker →
        normalGen U≤dN) →
    (Nat.card {f : G →* Q // Function.Surjective f} : ℝ)≤
      κ₃*(genRank G : ℝ)^κ₄*
        (Nat.card (Subgroup.centralizer (F : Set Q)) : ℝ)^genRank G*
        (Nat.card (⁅F,(⊤ : Subgroup Q)⁆ : Subgroup Q) : ℝ)^dN

/-- The target normal subgroup is never silently specialized to Q. -/
def targetCentralizer {Q : Type} [Group Q] (F : Subgroup Q) : Subgroup Q :=
  Subgroup.centralizer (F : Set Q)
def targetCommutator {Q : Type} [Group Q] (F : Subgroup Q) : Subgroup Q :=
  ⁅F,⊤⁆

end SymmetricSubgroupAsymptotics.MarkedC4.RDTNormalFInterface
