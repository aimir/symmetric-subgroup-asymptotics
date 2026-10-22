import SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels

/-! The first two original chain nodes are fixed by the literal D-fork
twist in every rank at least four. Their roots belong to the original
fixed subgroup; derived membership is supplied only by explicit words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreFixedRootElements
open CFSGSerreOrdinaryTwists

def node (s : ℕ) (i : Fin 2) : Fin (s + 4) := ⟨i.val, by have := i.isLt; omega⟩

theorem node_fixed (s : ℕ) (i : Fin 2) : CFSG.Models.dTwist (node s i) = node s i := by
  have hi := i.isLt
  have h2 : 2 ≤ s + 4 := by omega
  have ha : (node s i).val ≠ (s + 4) - 2 := by dsimp only [node]; omega
  have hb : (node s i).val ≠ (s + 4) - 1 := by dsimp only [node]; omega
  simp only [CFSG.Models.dTwist, dif_pos h2, if_neg ha, if_neg hb]

abbrev Fixed (s : ℕ) (q : CFSG.PrimePower) :=
  fixedSubgroup (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist (fun _ => q.order)
abbrev Derived (s : ℕ) (q : CFSG.PrimePower) := commutator (Fixed s q)

def root (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) (ht : definingFieldAutomorphism q 2 t = t) : Fixed s q :=
  fixedRoot (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) neg (node s i) t (node_fixed s i)
    (by simpa only [definingFieldAutomorphism_apply] using ht)

def toModel (s : ℕ) (q : CFSG.PrimePower) :
    Fixed s q →* Model (CartanMatrix.D (s + 4)) (q.Extension 2) :=
  fixedToModel (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist (fun _ => q.order)

def derivedToOriginal (s : ℕ) (q : CFSG.PrimePower) :
    Derived s q →* Model (CartanMatrix.D (s + 4)) (q.Extension 2) :=
  derivedToModel (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist (fun _ => q.order)

@[simp] theorem toModel_root (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) (ht : definingFieldAutomorphism q 2 t = t) :
    toModel s q (root s q neg i t ht) =
      modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (node s i) t := rfl

theorem one_fixed (q : CFSG.PrimePower) : definingFieldAutomorphism q 2 1 = 1 := map_one _

def positiveWord (s : ℕ) (q : CFSG.PrimePower) : Derived s q :=
  derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) (root s q false 0 1 (one_fixed q)) (root s q false 1 1 (one_fixed q))

def negativeWord (s : ℕ) (q : CFSG.PrimePower) : Derived s q :=
  derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) (root s q true 1 1 (one_fixed q)) (root s q true 0 1 (one_fixed q))

def weylWord (s : ℕ) (q : CFSG.PrimePower) : Derived s q :=
  (positiveWord s q)⁻¹ * negativeWord s q * (positiveWord s q)⁻¹

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
