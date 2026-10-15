import SymmetricSubgroupAsymptotics.CyclicImageNormalAxisGenerators
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductModels

/-! Every original quotient of literal A4 × C2 has a normally cyclic
socle. The existing normal-axis theorem is used with its actual Klein
kernel and its actual cyclic-six quotient map. The product's normal
subgroups are not asserted to form a chain. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSocles

open Non2UnipotentPrefixFiniteMenu.CentralBinaryProductModels

abbrev A4 := NaturalA4ScalarFourHead.G
abbrev C2 := Multiplicative (ZMod 2)
abbrev Model := A4 × C2

instance cyclicImage : IsCyclic (CyclicThree × C2) :=
  Group.isCyclic_prod_iff.mpr ⟨inferInstance,inferInstance,by
    change Nat.Coprime (Nat.card (Multiplicative (ZMod 3)))
      (Nat.card (Multiplicative (ZMod 2)))
    norm_num [Nat.card_eq_fintype_card]⟩

instance cyclicAxis : IsCyclic a4Core.central := by
  apply isCyclic_of_injective
    ((MonoidHom.snd A4 C2).comp a4Core.central.subtype)
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact ((a4Core.mem_central x.1).mp x.2).trans
      ((a4Core.mem_central y.1).mp y.2).symm
  · exact h

theorem kernel_not_le_axis : ¬ a4ProductTop.ker ≤ a4Core.central := by
  have hV : a4Core.V ≠ ⊥ := by
    rw [a4Core_eq_topKernel,NaturalA4ScalarFourHead.top_ker]
    intro h
    have hcard := alternatingGroup.kleinFour_card_of_card_eq_four
      (α := Fin 4) (by simp)
    rw [h] at hcard
    norm_num at hcard
  obtain ⟨v,hv,hvne⟩ := a4Core.V.bot_or_exists_ne_one.resolve_left hV
  intro h
  have hk : (v,(1 : C2)) ∈ a4ProductTop.ker := by
    rw [a4ProductTop_ker]
    exact (a4Core.mem_core _).mpr ⟨hv,rfl⟩
  exact hvne ((a4Core.mem_central _).mp (h hk))

theorem normal_generating_singletons :
    ∀ N : Subgroup Model, N.Normal →
      ∃ x : Fin 1 → Model, Subgroup.normalClosure (Set.range x) = N := by
  apply normal_generating_singletons_of_cyclic_image_axis
    a4ProductTop a4ProductTop_surjective a4Core.central kernel_not_le_axis
  intro N hN
  rw [a4ProductTop_ker]
  exact a4Core.normal_contains_core_or_le_central N hN

theorem quotientSocle (N : Subgroup Model) [N.Normal] :
    SocleNormalGeneratorBound (Model ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    normal_generating_singletons N

theorem socle_of_surjective {Q : Type} [Group Q]
    (pi : Model →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective pi hpi) (quotientSocle pi.ker)

end SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSocles

end
