import SymmetricSubgroupAsymptotics.CentralQuotientAutomorphismDescent
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow

/-! The FULL original fixed group acts on the literal ReeF4/Tits model
through its actual derived subgroup and the FULL derived centre quotient.
No target automorphism is lifted and the ambient group is not replaced
by the derived subgroup. Derived ambient elements act by actual inners. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientCentralQuotientAction
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalPositiveSylow
open CentralQuotientAutomorphismDescent

theorem derivedReeHom_ker (m : ℕ) :
    (derivedReeHom m).ker = Subgroup.center (commutator (originalModelFixed m)) := by
  ext d
  change (originalReeEquiv m).symm
      (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))) d) = 1 ↔
    d ∈ Subgroup.center (commutator (originalModelFixed m))
  constructor
  · intro hd
    have he : (originalReeEquiv m).symm
        (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))) d) =
        (originalReeEquiv m).symm 1 := hd.trans (map_one (originalReeEquiv m).symm).symm
    exact (QuotientGroup.eq_one_iff _).mp ((originalReeEquiv m).symm.injective he)
  · intro hd
    have he : (QuotientGroup.mk'
        (Subgroup.center (commutator (originalModelFixed m)))) d = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hd
    exact (congrArg (originalReeEquiv m).symm he).trans
      (map_one (originalReeEquiv m).symm)

def ambientAction (m : ℕ) : originalModelFixed m →* MulAut (CFSG.Models.ReeF4 m) :=
  (quotientMulAutHom (derivedReeHom m) (derivedReeHom_surjective m)
    (derivedReeHom_ker m)).comp MulAut.conjNormal

theorem ambientAction_apply (m : ℕ) (g : originalModelFixed m)
    (d : commutator (originalModelFixed m)) :
    ambientAction m g (derivedReeHom m d) =
      derivedReeHom m (MulAut.conjNormal g d) :=
  quotientMulAutHom_apply (derivedReeHom m) (derivedReeHom_surjective m)
    (derivedReeHom_ker m) (MulAut.conjNormal g) d

private theorem inner_of_intertwining
    {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal]
    (pi : N →* H) (hpi : Function.Surjective pi) (rho : G →* MulAut H)
    (he : ∀ g : G, ∀ n : N, rho g (pi n) = pi (MulAut.conjNormal g n))
    (d : N) : rho d = MulAut.conj (pi d) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨n, rfl⟩ := hpi x
  rw [he]
  have hn : MulAut.conjNormal (d : G) n = d * n * d⁻¹ := Subtype.ext rfl
  rw [hn, map_mul, map_mul, map_inv]
  rfl

theorem ambientAction_of_derived (m : ℕ) (d : commutator (originalModelFixed m)) :
    ambientAction m (d : originalModelFixed m) = MulAut.conj (derivedReeHom m d) :=
  inner_of_intertwining (commutator (originalModelFixed m)) (derivedReeHom m)
    (derivedReeHom_surjective m) (ambientAction m) (ambientAction_apply m) d

theorem ambientAction_map (m : ℕ) (g : originalModelFixed m)
    (P : Subgroup (commutator (originalModelFixed m))) :
    (P.map (MulAut.conjNormal g).toMonoidHom).map (derivedReeHom m) =
      (P.map (derivedReeHom m)).map (ambientAction m g).toMonoidHom := by
  have he : (derivedReeHom m).comp (MulAut.conjNormal g).toMonoidHom =
      (ambientAction m g).toMonoidHom.comp (derivedReeHom m) := by
    ext d
    exact (ambientAction_apply m g d).symm
  rw [Subgroup.map_map, Subgroup.map_map, he]

end SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientCentralQuotientAction
