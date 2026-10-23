import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPositive
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoefficientMap
import SymmetricSubgroupAsymptotics.CFSGHeisenbergEmbeddingIndex
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily

/-! The prime-field Heisenberg coordinates inject into the SAME original
projective Serre group. Both maps are explicit: entrywise prime-field
coefficients followed by literal positive-root products and the checked
original projection, injective on the actual positive group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergOriginal
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalHeisenbergRootPilot CFSGHeisenbergCoordinateGroup
open CFSGExceptionalHeisenbergPositive CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateOriginalProjection
open CFSGGeckSerreRepresentation
variable {r m:ℕ}(A:Matrix (Fin r) (Fin r) ℤ)(hd:∀i,A i i=2)
  (hs:A.transpose=A)(hp:(rationalMatrix A).PosDef)(ho:∀i j,i≠j→A i j≤0)
  [Fintype (Roots A)][DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced][(rootPairing A hs hp).IsIrreducible]
  (C:RootConfig A m)(K:Type)[Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def originalHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r) :
    Element K m→*Projective (cartan b₀ s₀) K :=
  ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K)).comp
    (positiveHom A hd hs hp ho C K)

theorem originalHom_injective [Finite K][Nontrivial (Fin r)]
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective (cartan b₀ s₀) K)](i:Fin r) :
    Function.Injective (originalHom A hd hs hp ho C K i) :=
  (originalProjection_positive_injective A hd hs hp ho K p i).comp
    (positiveHom_injective A hd hs hp ho C K)

def primeHom (p:ℕ)[Fact p.Prime][CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)](i:Fin r) :
    Element (ZMod p) m→*Projective (cartan b₀ s₀) K :=
  (originalHom A hd hs hp ho C K i).comp
    (CFSGHeisenbergCoefficientMap.map (ZMod.castHom (dvd_refl p) K))

theorem primeHom_injective [Finite K][Nontrivial (Fin r)]
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective (cartan b₀ s₀) K)](i:Fin r) :
    Function.Injective (primeHom A hd hs hp ho C K p i) :=
  (originalHom_injective A hd hs hp ho C K p i).comp
    (CFSGHeisenbergCoefficientMap.map_injective _ (ZMod.castHom (dvd_refl p) K).injective)

include C in
theorem prime_power_le_proper_index [Finite K][Nontrivial (Fin r)]
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective (cartan b₀ s₀) K)](i:Fin r)
    (H:Subgroup (Projective (cartan b₀ s₀) K))(hH:H≠⊤) : p^(m+1)≤H.index := by
  letI : Finite (Projective (cartan b₀ s₀) K) :=
    CFSGNormTwoCoordinateOriginalRootFamily.original_projective_finite A hd hs hp ho K i
  exact CFSGHeisenbergEmbeddingIndex.proper_index_least p m
    (primeHom A hd hs hp ho C K p i) (primeHom_injective A hd hs hp ho C K p i) H hH

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergOriginal
