import SymmetricSubgroupAsymptotics.SixteenPointNonPairOriginalChart
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! The exact nonpair point chart transports an original stabilizer
epimorphism and its representation, as well as each original normal
subgroup. The local map is composed with the inverse stabilizer chart;
it is never replaced by the internal component map of a second block system. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.SixteenPointNonPairOriginalChart

variable {X : Type} [Finite X] {S : Subgroup (Equiv.Perm X)}
    (C : SixteenPointNonPairOriginalChart S)

def localMap {L : Type} [Group L] (x : X)
    (f : MulAction.stabilizer S x →* L) :
    MulAction.stabilizer (preE7NonPairAction 16 C.index) (C.points x) →* L :=
  f.comp (C.stabilizerEquiv x).symm.toMonoidHom

theorem localMap_surjective {L : Type} [Group L] (x : X)
    (f : MulAction.stabilizer S x →* L) (hf : Function.Surjective f) :
    Function.Surjective (C.localMap x f) :=
  hf.comp (C.stabilizerEquiv x).symm.surjective

def localRepresentationEquiv {k L V : Type} [Field k] [Group L]
    [AddCommGroup V] [Module k V] (x : X)
    (f : MulAction.stabilizer S x →* L) (rho : Representation k L V) :
    Representation.Equiv (rho.comp f)
      ((rho.comp (C.localMap x f)).comp (C.stabilizerEquiv x).toMonoidHom) :=
  Representation.Equiv.mk (LinearEquiv.refl k V) (by
    intro h
    apply LinearMap.ext
    intro v
    change rho (f h) v =
      rho (f ((C.stabilizerEquiv x).symm ((C.stabilizerEquiv x) h))) v
    rw [MulEquiv.symm_apply_apply])

/-- Uniform local heads transfer through the same original point chart. -/
theorem uniform_head_le {k L V : Type} [Field k] [Group L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (x : X) (f : MulAction.stabilizer S x →* L) (rho : Representation k L V)
    (cap : ℕ)
    (hcap : ∀ A : Subrepresentation
      (Representation.coind
        (MulAction.stabilizer (preE7NonPairAction 16 C.index) (C.points x)).subtype
        (rho.comp (C.localMap x f))),
      Module.finrank k (A.toRepresentation.IntertwiningMap
        (Representation.trivial k (preE7NonPairAction 16 C.index) k)) ≤ cap)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer S x).subtype (rho.comp f))) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k S k)) ≤ cap :=
  CoinducedGroupLocalTransport.uniform_head_le
    (MulAction.stabilizer S x)
    (MulAction.stabilizer (preE7NonPairAction 16 C.index) (C.points x))
    C.groupEquiv (C.stabilizerEquiv x) (C.stabilizerEquiv_commutes x)
    (rho.comp f) (rho.comp (C.localMap x f))
    (C.localRepresentationEquiv x f rho) cap hcap B

/-- Each normal axis is mapped by the actual ambient point chart. -/
theorem relative_head_le (p : ℕ) [Fact p.Prime] (cap : ℕ)
    (htarget : ∀ (M : Subgroup (preE7NonPairAction 16 C.index)) [M.Normal],
      Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤ cap)
    (N : Subgroup S) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ cap := by
  let M := N.map C.groupEquiv.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ C.groupEquiv.surjective
  rw [← (relativeCharacterAmbientCongr p C.groupEquiv N M rfl).finrank_eq]
  exact htarget M

end Non2UnipotentPrefixFiniteMenu.SixteenPointNonPairOriginalChart
end SymmetricSubgroupAsymptotics

end
