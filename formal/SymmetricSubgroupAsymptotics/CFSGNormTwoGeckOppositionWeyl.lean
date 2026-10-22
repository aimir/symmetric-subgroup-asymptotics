import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive

/-! Opposition swaps the two actual root groups and sends each actual
simple Weyl word to its inverse. Opposition is used only as an ambient
matrix unit; no membership in the generated group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionWeyl
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckFieldOpposition CFSGNormTwoGeckSelfRootConjugation
open CFSGSerreQuadraticMatrix
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem opposition_inverse (K : Type) [Field K] :
    (oppositionUnit A hs hp b K)⁻¹=oppositionUnit A hs hp b K := by
  apply Units.ext
  rfl

theorem opposition_rootGroup_eq (K : Type) [Field K] (neg : Bool) :
    (rootGroup A hs hp b s K neg).map
      (MulAut.conj (oppositionUnit A hs hp b K)).toMonoidHom=
        rootGroup A hs hp b s K (!neg) := by
  rw [rootGroup,MonoidHom.map_closure,rootGroup]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨z,(canonicalRoot_conjugate A hs hp b s K neg z.1 z.2).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨canonicalRoot (realizationData A hs hp b s) K neg z.1 z.2,⟨z,rfl⟩,
      canonicalRoot_conjugate A hs hp b s K neg z.1 z.2⟩

theorem opposition_conjugate_mem (K : Type) [Field K] (neg : Bool)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K neg) :
    oppositionUnit A hs hp b K*g*(oppositionUnit A hs hp b K)⁻¹∈
      rootGroup A hs hp b s K (!neg) := by
  rw [←opposition_rootGroup_eq A hs hp b s K neg]
  exact ⟨g,hg,rfl⟩

theorem weyl_reverse_word (K : Type) [Field K] (i : Fin r) :
    canonicalWeyl (realizationData A hs hp b s) K i=
      canonicalRoot (realizationData A hs hp b s) K true i (-1)*
        canonicalRoot (realizationData A hs hp b s) K false i 1*
          canonicalRoot (realizationData A hs hp b s) K true i (-1) := by
  let u := canonicalRoot (realizationData A hs hp b s) K false i 1
  let v := canonicalRoot (realizationData A hs hp b s) K true i (-1)
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  have hw : w=u*v*u := rfl
  have hc : w*u*w⁻¹=v := self_root_word A hs hp b s K i 1
  have hcomm : w*u=v*w := by
    calc
      w*u=(w*u*w⁻¹)*w := by group
      _=v*w := by rw [hc]
  change w=v*u*v
  calc
    w=(w*u)*u⁻¹ := by group
    _=(v*w)*u⁻¹ := by rw [hcomm]
    _=v*u*v := by rw [hw];group

theorem opposition_weyl (K : Type) [Field K] (i : Fin r) :
    oppositionUnit A hs hp b K*
      canonicalWeyl (realizationData A hs hp b s) K i*
        (oppositionUnit A hs hp b K)⁻¹=
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹ := by
  let u := canonicalRoot (realizationData A hs hp b s) K false i 1
  let v := canonicalRoot (realizationData A hs hp b s) K true i (-1)
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  let o := oppositionUnit A hs hp b K
  have hu : o*u*o⁻¹=v⁻¹ := by
    simpa only [u,v,o,canonicalRoot_inverse,neg_neg] using
      canonicalRoot_conjugate A hs hp b s K false i 1
  have hv : o*v*o⁻¹=u⁻¹ := by
    simpa only [u,v,o,canonicalRoot_inverse] using
      canonicalRoot_conjugate A hs hp b s K true i (-1)
  have hw : w=u*v*u := rfl
  have hr : w=v*u*v := weyl_reverse_word A hs hp b s K i
  change o*w*o⁻¹=w⁻¹
  calc
    o*w*o⁻¹=(o*u*o⁻¹)*(o*v*o⁻¹)*(o*u*o⁻¹) := by rw [hw];group
    _=v⁻¹*u⁻¹*v⁻¹ := by rw [hu,hv]
    _=w⁻¹ := by rw [hr];group

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionWeyl
