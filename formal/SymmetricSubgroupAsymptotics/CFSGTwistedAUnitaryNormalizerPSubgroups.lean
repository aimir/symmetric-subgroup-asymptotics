import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizerMatrices
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryTriangularSimilitude
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularPSubgroups
import Mathlib.GroupTheory.Sylow

/-! Every defining-characteristic p-subgroup of the SAME ORIGINAL upper
normalizer lies in the actual original upper subgroup. Sylow lifting in
the genuine finite natural pullback supplies the diagonal-one witnesses;
no splitting of a central quotient or ambient unitary order is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem pGroup_upper_diagonal_one {K G : Type} [Field K] [Group G]
    (r p : ℕ) [Fact p.Prime] [CharP K p] (hG : IsPGroup p G)
    (rho : G →* Mat K r) (hupper : ∀ g, (rho g).BlockTriangular id)
    (g : G) (i : Fin (r + 1)) : rho g i i = 1 := by
  obtain ⟨k, hk⟩ := hG g
  have hp : rho g ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have he := congrArg (fun M : Mat K r => M i i) hp
  dsimp only at he
  rw [CFSGUpperUnitriangular.upper_diag_pow (hupper g), Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def, one_pow] using he

theorem originalFixed_finite (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    Finite (Fixed r q) := by
  letI : Finite (fixedNaturalPullback r q) :=
    Finite.of_injective (pullbackMatrix r q) (pullbackMatrix_injective q r)
  exact Finite.of_surjective (pullbackSource r q) (pullbackSource_surjective r hr q)

theorem original_normalizer_pSubgroups (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (P : Subgroup (Fixed r q)) (hP : IsPGroup q.prime P)
    (hPN : P ≤ Subgroup.normalizer (originalUnipotent r q : Set (Fixed r q))) :
    P ≤ originalUnipotent r q := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  letI : Finite (fixedNaturalPullback r q) :=
    Finite.of_injective (pullbackMatrix r q) (pullbackMatrix_injective q r)
  let R := P.comap (pullbackSource r q)
  let f : R →* P :=
    { toFun := fun u => ⟨pullbackSource r q u.val, u.property⟩
      map_one' := by apply Subtype.ext; exact map_one (pullbackSource r q)
      map_mul' := fun u v => by apply Subtype.ext; exact map_mul (pullbackSource r q) u.val v.val }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨u, hu⟩ := pullbackSource_surjective r hr q g.val
    refine ⟨⟨u, ?_⟩, ?_⟩
    · change pullbackSource r q u ∈ P
      rw [hu]
      exact g.property
    · exact Subtype.ext hu
  let S : Sylow q.prime R := default
  have htop : ((S.mapSurjective hf : Sylow q.prime P) : Subgroup P) = ⊤ :=
    ((S.mapSurjective hf).3 (hP.to_subgroup ⊤) le_top).symm
  intro g hg
  have hgmap : (⟨g, hg⟩ : P) ∈ (S : Subgroup R).map f := by
    rw [← Sylow.coe_mapSurjective hf S, htop]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, he⟩ := hgmap
  let rho : S →* Mat (q.Extension 2) r :=
    (Units.coeHom (Mat (q.Extension 2) r)).comp
      ((pullbackMatrix r q).comp (R.subtype.comp (S : Subgroup R).subtype))
  have hupper (x : S) : (rho x).BlockTriangular id :=
    pullback_normalizer_upper q r hr x.val.val (hPN x.val.property)
  have hd : ∀ i, (pullbackMatrix r q u.val : Mat (q.Extension 2) r) i i = 1 := by
    intro i
    exact pGroup_upper_diagonal_one r q.prime S.isPGroup' rho hupper ⟨u, hu⟩ i
  have hm := pullbackSource_mem_unipotent_of_unitriangular q r hr u.val
    (hupper ⟨u, hu⟩) hd
  have he' : pullbackSource r q u.val = g := congrArg (fun x : P => x.val) he
  rw [he'] at hm
  exact hm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
