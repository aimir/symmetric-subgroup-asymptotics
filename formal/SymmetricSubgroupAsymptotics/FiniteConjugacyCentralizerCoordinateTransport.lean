import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCoordinates

/-!
# Transport selected centralizer coordinates across a group equivalence

The bounded witness is checked in an executable finite-row group and then
identified with the literal permutation subgroup.  This file transports the
actual centralizers and their reversible kernel/range charts.  It does not
replace the original action by an unrelated isomorphic group: the supplied
equivalence is the checked Cayley reflection into that literal subgroup.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- A group equivalence restricts to the centralizers of corresponding
literal elements. -/
def centralizerSingletonMulEquiv (e : G ≃* H) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃*
      Subgroup.centralizer ({e g} : Set H) where
  toFun x := ⟨e (x : G), by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.property
    simpa only [map_mul] using congrArg e hx⟩
  invFun y := ⟨e.symm (y : H), by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hy := Subgroup.mem_centralizer_singleton_iff.mp y.property
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : G))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : H))
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

/-- Precomposition by an equivalence identifies the two literal kernels. -/
def kerCompMulEquiv (f : G →* K) (e : G ≃* H) :
    (f.comp e.symm.toMonoidHom).ker ≃* f.ker where
  toFun x := ⟨e.symm (x : H), by exact x.property⟩
  invFun y := ⟨e (y : G), by
    change f (e.symm (e (y : G))) = 1
    simpa only [e.symm_apply_apply] using y.property⟩
  left_inv x := Subtype.ext (e.apply_symm_apply (x : H))
  right_inv y := Subtype.ext (e.symm_apply_apply (y : G))
  map_mul' x y := Subtype.ext (map_mul e.symm (x : H) (y : H))

/-- Precomposition by a surjective equivalence leaves the literal range
subgroup unchanged. -/
theorem range_comp_mulEquiv (f : G →* K) (e : G ≃* H) :
    (f.comp e.symm.toMonoidHom).range = f.range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨e.symm x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨e x, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply]

namespace FinitePairCentralizerCoordinateCertificate

variable [Finite G] [Finite H] {C : Subgroup G} {w : ℕ}
    (D : FinitePairCentralizerCoordinateCertificate C w)

/-- Transport one reversible coordinate certificate to the corresponding
centralizer in the literal target group. -/
noncomputable def mapCentralizerEquiv (e : G ≃* H) (g : G)
    (hC : C = Subgroup.centralizer ({g} : Set G)) :
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({e g} : Set H)) w := by
  subst C
  let ce := centralizerSingletonMulEquiv e g
  let transportedTop :
      Subgroup.centralizer ({e g} : Set H) →* Equiv.Perm (Fin w) :=
    D.top.comp ce.symm.toMonoidHom
  exact {
    top := transportedTop
    kernelCard := D.kernelCard
    topCard := D.topCard
    claimedCard := D.claimedCard
    kernelChart := (kerCompMulEquiv D.top ce).toEquiv.trans D.kernelChart
    topChart := (MulEquiv.subgroupCongr
      (range_comp_mulEquiv D.top ce)).toEquiv.trans D.topChart
    product_card := D.product_card }

end FinitePairCentralizerCoordinateCertificate

namespace FiniteConjugacyCentralizerCoordinateChunk

variable [Finite G] [Finite H] {c w : ℕ} {representative : Fin c → G}
    (D : FiniteConjugacyCentralizerCoordinateChunk representative w)

/-- Transport the whole checked conjugacy chunk to the corresponding literal
group.  The class sum is preserved by the same equivalence. -/
noncomputable def mapEquiv (e : G ≃* H) :
    FiniteConjugacyCentralizerCoordinateChunk
      (fun i => e (representative i)) w where
  separated := by
    intro i j hij
    apply D.separated i j
    have h := e.symm.toMonoidHom.map_isConj hij
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h
  centralizer i :=
    (D.centralizer i).mapCentralizerEquiv e (representative i) rfl
  claimed_class_sum := by
    have hcard : Nat.card G = Nat.card H := Nat.card_congr e.toEquiv
    change (∑ i : Fin c,
      Nat.card H / (D.centralizer i).claimedCard) = Nat.card H
    rw [← hcard]
    exact D.claimed_class_sum

end FiniteConjugacyCentralizerCoordinateChunk

end SymmetricSubgroupAsymptotics

end
