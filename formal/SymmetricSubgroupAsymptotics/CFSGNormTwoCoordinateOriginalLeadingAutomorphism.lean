import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingSurjective
import SymmetricSubgroupAsymptotics.CFSGDerivedCoordinateAutomorphism

/-! Every automorphism of the ACTUAL original positive subgroup induces
an actual additive coordinate automorphism. No semilinearity or axis
preservation is assumed here; those require the intrinsic root family. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingAutomorphism
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalLeadingHom CFSGNormTwoCoordinateLeadingSurjective
open CFSGDerivedCoordinateAutomorphism
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem originalLeadingHom_surjective (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Function.Surjective (originalLeadingHom A hd hs hp ho K p i) := by
  intro c
  obtain ⟨u,hu⟩ := leadingHom_surjective A hd hs hp ho K c
  exact ⟨(originalPositiveEquiv A hd hs hp ho K p i) u,
    (originalLeadingHom_equiv_apply A hd hs hp ho K p i u).trans hu⟩

def originalLeadingAut (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (originalPositive A hd hs hp ho K i)) : MulAut (Multiplicative (Fin r→K)) :=
  coordinateAut (originalLeadingHom A hd hs hp ho K p i)
    (originalLeadingHom_surjective A hd hs hp ho K p i)
    (originalLeadingHom_kernel A hd hs hp ho K p i) f

theorem originalLeadingAut_apply (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (originalPositive A hd hs hp ho K i)) (u : originalPositive A hd hs hp ho K i) :
    originalLeadingAut A hd hs hp ho K p i f (originalLeadingHom A hd hs hp ho K p i u)=
      originalLeadingHom A hd hs hp ho K p i (f u) :=
  coordinateAut_apply _ _ _ f u

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingAutomorphism
