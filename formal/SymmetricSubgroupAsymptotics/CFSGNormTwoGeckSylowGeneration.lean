import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration

/-! Actual two-conjugate-Sylow generation of the canonical finite Geck
matrix group. The positive/negative groups need not be Sylow, and the
opposition matrix need not belong to this group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSylowGeneration
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix CFSGNormTwoGeckPositivePGroup
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem canonical_two_conjugate_sylows (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃(P : Sylow p (canonicalElementaryGroup (realizationData A hs hp b s) K))
      (g : canonicalElementaryGroup (realizationData A hs hp b s) K),
      Subgroup.closure ((P : Set (canonicalElementaryGroup (realizationData A hs hp b s) K)) ∪
        (P : Subgroup (canonicalElementaryGroup (realizationData A hs hp b s) K)).map
          (MulAut.conj g).toMonoidHom)=⊤ := by
  letI : Fintype K := Fintype.ofFinite K
  let H := canonicalElementaryGroup (realizationData A hs hp b s) K
  let U := rootGroup A hs hp b s K false
  let V := rootGroup A hs hp b s K true
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b s K
  have hU : U≤H := by rw [←hjoin];exact le_sup_left
  have hV : V≤H := by rw [←hjoin];exact le_sup_right
  have hUp : IsPGroup p (U.subgroupOf H) :=
    (positive_isPGroup A hs hp b s height hheight K p).of_injective
      (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom (Subgroup.subgroupOfEquivOfLe hU).injective
  have hVp : IsPGroup p (V.subgroupOf H) :=
    (negative_isPGroup A hs hp b s height hheight K p).of_injective
      (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom (Subgroup.subgroupOfEquivOfLe hV).injective
  have htop : U.subgroupOf H⊔V.subgroupOf H=⊤ := by
    rw [←Subgroup.subgroupOf_sup hU hV,hjoin,Subgroup.subgroupOf_self]
  obtain ⟨P,g,_,hg⟩ := CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows
    (U.subgroupOf H) (V.subgroupOf H) hUp hVp htop
  exact ⟨P,g,hg⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSylowGeneration
