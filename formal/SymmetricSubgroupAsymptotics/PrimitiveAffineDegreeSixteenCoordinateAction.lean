import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.ElementaryZModAutomorphismCoordinates
import SymmetricSubgroupAsymptotics.GeneralFourTwoMatrixEncoding
import Mathlib.Tactic.Group

/-! Actual four-dimensional coordinates for a primitive affine sixteen-point
profile. The prime and dimension follow from the original translation
cardinality; every invariant coordinate space pulls back to a normal
subgroup of the SAME original regular translation group. No finite
catalogue or complement classification is used. Proofs specialize the
already checked degree-eight coordinate construction at dimension four. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix IsMulCommutative

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

private theorem degreeSixteen_primePower_unique
    {p q d e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (he : 0 < e) (h : p ^ d = q ^ e) : p = q ∧ d = e := by
  have hpdiv : p ∣ q := hp.dvd_of_dvd_pow (by
    rw [← h]
    exact dvd_pow_self p hd.ne')
  have hqdiv : q ∣ p := hq.dvd_of_dvd_pow (by
    rw [h]
    exact dvd_pow_self q he.ne')
  have hpq : p = q := Nat.dvd_antisymm hpdiv hqdiv
  subst q
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

variable {L Ω : Type} [Group L] [MulAction L Ω] [Finite L]
  [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]

theorem degreeSixteen_prime_dimension (P : PrimitiveAffineProfile L Ω)
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω) (hdegree : Nat.card Ω = 16) :
    P.p = 2 ∧ (P.elementaryChart hprimitive).d = 4 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hcard : Nat.card Ω = P.p ^ Module.finrank (ZMod P.p) C.V := by
    calc
      Nat.card Ω = Nat.card P.V := (P.card_eq x).symm
      _ = Nat.card C.V := Nat.card_congr C.equiv.toEquiv
      _ = P.p ^ Module.finrank (ZMod P.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := C.V), Nat.card_zmod]
  have hpower : P.p ^ C.d = 2 ^ 4 := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d, hdegree] using hcard.symm
  exact degreeSixteen_primePower_unique P.p_prime (by norm_num : Nat.Prime 2)
    C.d_pos (by norm_num) hpower

/-- The matrix homomorphism is constructed from the actual conjugation
representation on the actual elementary translation chart. -/
theorem exists_complementLinearEmbedding_degreeSixteen
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 16) :
    ∃ phi : P.complement x →*
        GeneralFourTwoMatrixEncoding.Ambient,
      Function.Injective phi := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  have hp_hd := P.degreeSixteen_prime_dimension hprimitive x hdegree
  have hp : P.p = 2 := hp_hd.1
  have hfin : Module.finrank (ZMod P.p) C.V = 4 := by
    simpa [C, PrimitiveAffineProfile.ElementaryChart.d] using hp_hd.2
  let basis : Module.Basis (Fin 4) (ZMod P.p) C.V :=
    Module.finBasisOfFinrankEq (ZMod P.p) C.V hfin
  let rho := (P.complementRepresentationCore hprimitive C x).ρ
  let phi0 : P.complement x →* Matrix.GeneralLinearGroup (Fin 4) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hphi0 : Function.Injective phi0 := by
    intro a b hab
    apply P.complementRepresentationCore_injective hprimitive C x
    have hab' : Representation.asGroupHom rho a = Representation.asGroupHom rho b := by
      exact (Matrix.GeneralLinearGroup.toLin' basis).symm.injective (by
        simpa [phi0] using hab)
    exact congrArg Units.val hab'
  let e : ZMod P.p ≃+* ZMod 2 := ZMod.ringEquivCongr hp
  let phi : P.complement x →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0
  refine ⟨phi, ?_⟩
  intro a b hab
  apply hphi0
  apply Units.ext
  ext i j
  apply e.injective
  have hij := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) => g i j) hab
  simpa [phi] using hij

noncomputable def complementLinearMap_degreeSixteen
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 16) :
    P.complement x →* GeneralFourTwoMatrixEncoding.Ambient :=
  Classical.choose (P.exists_complementLinearEmbedding_degreeSixteen hprimitive x hdegree)

theorem complementLinearMap_degreeSixteen_injective
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 16) :
    Function.Injective (P.complementLinearMap_degreeSixteen hprimitive x hdegree) :=
  Classical.choose_spec (P.exists_complementLinearEmbedding_degreeSixteen hprimitive x hdegree)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile


namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]

private def withPrimeTwoSixteen (P : PrimitiveAffineProfile L Ω) (hp : P.p = 2) :
    PrimitiveAffineProfile L Ω where
  p := 2
  p_prime := by decide
  V := P.V
  V_normal := P.V_normal
  V_pgroup := by rw [← hp]; exact P.V_pgroup
  regular := P.regular

theorem translationCoordinates_degreeSixteen_nonempty
    [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 16) :
    Nonempty (P.V ≃* Multiplicative (Fin 4 → ZMod 2)) := by
  have hp := (P.degreeSixteen_prime_dimension hprimitive x hdegree).1
  let Q := withPrimeTwoSixteen P hp
  let C := Q.elementaryChart hprimitive
  letI : Fact (Nat.Prime 2) := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod 2) C.V := C.module
  letI : FiniteDimensional (ZMod 2) C.V := C.finiteDimensional
  have hfin : Module.finrank (ZMod 2) C.V = 4 := by
    simpa only [ElementaryChart.d] using
      (Q.degreeSixteen_prime_dimension hprimitive x hdegree).2
  let basis : Module.Basis (Fin 4) (ZMod 2) C.V :=
    Module.finBasisOfFinrankEq (ZMod 2) C.V hfin
  exact ⟨C.equiv.trans basis.equivFun.toAddEquiv.toMultiplicative⟩

/-- Every supplied actual translation chart determines a faithful matrix
map of the actual point stabilizer, with no arbitrary representation choice. -/
def complementCoordinateMapSixteen (P : PrimitiveAffineProfile L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 4 → ZMod 2)) :
    P.complement x →* GeneralFourTwoMatrixEncoding.Ambient :=
  (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 4).toMonoidHom.comp
    ((MulAut.congr a).toMonoidHom.comp (P.complementAction x))

theorem complementCoordinateMapSixteen_injective [FaithfulSMul L Ω]
    (P : PrimitiveAffineProfile L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 4 → ZMod 2)) :
    Function.Injective (P.complementCoordinateMapSixteen x a) :=
  (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 4).injective.comp
    ((MulAut.congr a).injective.comp (P.complementAction_injective x))

/-- The matrix action is exactly conjugation on the original translations
under the specified coordinates. -/
theorem complementCoordinateMapSixteen_action
    (P : PrimitiveAffineProfile L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 4 → ZMod 2))
    (k : P.complement x) (v : P.V) :
    (P.complementCoordinateMapSixteen x a k).val *ᵥ (a v).toAdd =
      (a (P.complementAction x k v)).toAdd := by
  change (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 4
    ((MulAut.congr a) (P.complementAction x k))).val *ᵥ (a v).toAdd = _
  rw [ElementaryZModAutomorphismCoordinates.matrixEquiv_apply]
  change (a (P.complementAction x k (a.symm (a v)))).toAdd = _
  rw [a.symm_apply_apply]

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile


namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  [Finite L] [Finite Ω] [Nontrivial Ω]
  (P : PrimitiveAffineProfile L Ω)

private theorem degreeSixteen_conjugate_translation
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (u : P.V ⋊[P.complementAction x] P.complement x) (v : P.V) :
    P.semidirectEquiv x u * (v : L) * (P.semidirectEquiv x u)⁻¹ =
      (P.complementAction x u.right v : L) := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  have hcomm := congrArg Subtype.val
    (mul_comm u.left (P.complementAction x u.right v))
  change (u.left : L) * ((u.right : L) * (v : L) * (u.right : L)⁻¹) =
    ((u.right : L) * (v : L) * (u.right : L)⁻¹) * (u.left : L) at hcomm
  change ((u.left : L) * (u.right : L)) * (v : L) *
      ((u.left : L) * (u.right : L))⁻¹ =
    (u.right : L) * (v : L) * (u.right : L)⁻¹
  calc
    _ = (u.left : L) * ((u.right : L) * (v : L) * (u.right : L)⁻¹) *
        (u.left : L)⁻¹ := by group
    _ = _ := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private def degreeSixteen_invariantTranslations (_x : Ω)
    (a : P.V ≃* Multiplicative (Fin 4 → ZMod 2))
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2)) : Subgroup P.V where
  carrier := {v | (a v).toAdd ∈ W}
  one_mem' := by simpa using W.zero_mem
  mul_mem' := by
    intro u v hu hv
    change (a (u * v)).toAdd ∈ W
    rw [map_mul]
    exact W.add_mem hu hv
  inv_mem' := by
    intro v hv
    change (a v⁻¹).toAdd ∈ W
    rw [map_inv]
    exact W.neg_mem hv

theorem invariantCoordinateSubmoduleSixteen_eq_bot_or_top
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 4 → ZMod 2))
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hstable : ∀ k : P.complement x, ∀ v ∈ W,
      (P.complementCoordinateMapSixteen x a k).val *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let K₀ : Subgroup P.V := degreeSixteen_invariantTranslations P x a W
  let K : Subgroup L := K₀.map P.V.subtype
  have hKnormal : K.Normal := by
    constructor
    intro y hy q
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨u, rfl⟩ := (P.semidirectEquiv x).surjective q
    refine ⟨P.complementAction x u.right v, ?_,
      (degreeSixteen_conjugate_translation P hprimitive x u v).symm⟩
    change (a (P.complementAction x u.right v)).toAdd ∈ W
    rw [← P.complementCoordinateMapSixteen_action x a u.right v]
    exact hstable u.right (a v).toAdd hv
  have hKle : K ≤ P.V := Subgroup.map_subtype_le K₀
  have hK := P.minimal hprimitive K hKnormal hKle
  have hK₀ : K₀ = ⊥ ∨ K₀ = ⊤ := by
    rcases hK with hbot | htop
    · exact Or.inl ((K₀.map_eq_bot_iff_of_injective P.V.subtype_injective).mp hbot)
    · right
      apply Subgroup.map_injective P.V.subtype_injective
      simpa only [K, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  rcases hK₀ with hbot | htop
  · left
    apply eq_bot_iff.mpr
    intro v hv
    let t : P.V := a.symm (Multiplicative.ofAdd v)
    have ht : t ∈ K₀ := by
      change (a t).toAdd ∈ W
      simpa [t] using hv
    rw [hbot] at ht
    have ht1 : t = 1 := Subgroup.mem_bot.mp ht
    apply (Submodule.mem_bot (R := ZMod 2)).mpr
    have he := congrArg (fun t : P.V => (a t).toAdd) ht1
    simpa [t] using he
  · right
    apply top_le_iff.mp
    intro v _
    let t : P.V := a.symm (Multiplicative.ofAdd v)
    have ht : t ∈ K₀ := by rw [htop]; exact Subgroup.mem_top t
    change (a t).toAdd ∈ W at ht
    simpa [t] using ht

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile


end
