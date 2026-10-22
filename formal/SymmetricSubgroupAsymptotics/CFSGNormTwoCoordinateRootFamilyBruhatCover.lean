import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootOrbitCardinality

/-! The whole actual conjugacy family of the dominant root is covered
by positive-group orbits of the finite, original lattice-root family.
The proof uses the checked whole Bruhat cover and actual torus action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyBruhatCover
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoCoordinateBruhatCover
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoCoordinateBorelRootNormalization CFSGSubgroupConjugateOrbitCardinality
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem root_conjugate_eq_positive_conjugate (K : Type) [Field K] (θ : Roots A)
    (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (g : ElementaryGroup A hd hs hp ho K) :
    ∃k : Roots A,∃u : PositiveGroup A hd hs hp ho K,
      (rootSubgroup A hd hs hp ho K θ).map (MulAut.conj g.val).toMonoidHom=
        (rootSubgroup A hd hs hp ho K k).map (MulAut.conj u.val).toMonoidHom := by
  obtain ⟨w,b,hb,c,hc,hg⟩ := canonical_bruhat_cover A hd hs hp ho K g.val g.property
  obtain ⟨u,hu,t,ht,hbval⟩ := borel_factor A hs hp b₀ s₀ K b hb
  let k : Roots A := wordRoot A hs hp b₀ s₀ w θ
  have hw : (rootSubgroup A hd hs hp ho K θ).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom=
        rootSubgroup A hd hs hp ho K k := by
    rw [word_eq_canonicalWord]
    exact rootSubgroup_map_word A hd hs hp ho K w θ
  have hc' := conjugate_eq_of_mem_normalizer (rootSubgroup A hd hs hp ho K θ) c
    (borel_le_normalizer_dominant_root A hd hs hp ho K θ hθ hdom hc)
  have ht' := conjugate_eq_of_mem_normalizer (rootSubgroup A hd hs hp ho K k) t
    (torusGroup_le_normalizer_root A hd hs hp ho K k ht)
  refine ⟨k,⟨u,hu⟩,?_⟩
  rw [hg,conjugate_mul,hc',conjugate_mul,hw,hbval,conjugate_mul,ht']

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyBruhatCover
