import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! A genuine surviving central point-radical root moves a coset of
every proper subgroup of the SAME literal simple symplectic quotient.
The SAME pulled-back stabilizer yields the uniform binary proper-index
bound, with no faithful whole-extension or action-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointIndex
open CFSGSymplecticSerreMatrices CFSGSymplecticBinaryPointExtension
open CFSGSymplecticBinaryPointStabilizerIndex
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hcard : Nat.card K = 2)

private theorem degree_of_central_motion (s : ℕ) (hs : 0 < s)
    {X : Type*} [Finite X] [MulAction (PointParabolic K hcard (s+1)) X]
    (x : X) (hx : (SemidirectProduct.inl (Multiplicative.ofAdd (0,(1 : K))) :
      PointParabolic K hcard (s+1)) • x ≠ x) :
    2^(s+1)*(2^(s+1)-1) ≤ Nat.card X := by
  let M := MulAction.stabilizer (PointParabolic K hcard (s+1)) x
  have hM : (SemidirectProduct.inl (Multiplicative.ofAdd (0,(1 : K))) :
      PointParabolic K hcard (s+1)) ∉ M := hx
  have hindex : M.index ≤ Nat.card X := by
    calc
      _ = Nat.card (MulAction.orbit (PointParabolic K hcard (s+1)) x) :=
        (Nat.card_congr
          (MulAction.orbitEquivQuotientStabilizer (PointParabolic K hcard (s+1)) x)).symm
      _ ≤ Nat.card X := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (semidirect_central_index_lower K hcard s hs M hM).trans hindex

private theorem proper_index_of_central_survival
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (s : ℕ) (hs : 0 < s) (F : PointParabolic K hcard (s+1) →* G)
    (hF : F (SemidirectProduct.inl (Multiplicative.ofAdd (0,(1 : K)))) ≠ 1)
    (H : Subgroup G) (hH : H ≠ ⊤) : 2^(s+1)*(2^(s+1)-1) ≤ H.index := by
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hF
  letI : MulAction (PointParabolic K hcard (s+1)) (G ⧸ H) := MulAction.compHom _ F
  have hb := degree_of_central_motion K hcard s hs x hx
  simpa only [Subgroup.index_eq_card] using hb

include hcard in
theorem binary_point_radical_proper_index (r : ℕ) (hr : 3 ≤ r)
    [IsSimpleGroup (elementaryProjective K r)]
    (H : Subgroup (elementaryProjective K r)) (hH : H ≠ ⊤) :
    2^(r-1)*(2^(r-1)-1) ≤ H.index := by
  obtain ⟨s,hs,rfl⟩ : ∃ s : ℕ, 0 < s ∧ r = s+2 := ⟨r-2,by omega,by omega⟩
  have h := proper_index_of_central_survival K hcard s hs
    (projectiveExtensionHom K hcard (s+1) (by omega))
    (projectiveExtensionHom_central_ne_one K hcard (s+1) (by omega)) H hH
  have he : s+2-1 = s+1 := by omega
  simpa only [he] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointIndex
