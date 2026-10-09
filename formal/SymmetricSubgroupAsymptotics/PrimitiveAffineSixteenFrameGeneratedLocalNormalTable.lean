import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedTopTable
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry

/-!
# Generated local catalogues from one source-stabilizer normal registry

The top-table importer should not need a bespoke quotient-classification
proof for each row.  A complete normal-state registry in the stored point
stabilizer suffices: states of index three and noncommutative index six must
be row kernels; all other states are irrelevant, except commutative
index-six quotients which cannot be faithful binary-plane targets.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Source-side normal-state certificate for every local row above one
generated top. -/
structure GeneratedSixteenSourceLocalNormalTable (T : GeneratedSixteenTopData) : Type 1 where
  Row : Type
  data : Row → GeneratedSixteenRowData T
  State : Type
  state : State → Subgroup T.sourceStabilizer
  complete : ∀ (N : Subgroup T.sourceStabilizer) [N.Normal],
    ∃ s, state s = N
  classify : ∀ s,
    (∃ r, state s = (data r).sourceLocalMap.ker) ∨
    ((state s).index ≠ 3 ∧ (state s).index ≠ 6) ∨
    ((state s).index = 6 ∧
      ∃ _normal : (state s).Normal,
        IsMulCommutative (T.sourceStabilizer ⧸ state s))

namespace GeneratedSixteenSourceLocalNormalTable

/-- Build the shared source-local catalogue directly from one finite
normal-join word registry.  This is the boundary used by generated files:
the producer emits conjugacy representatives, short subgroup generators,
and the local classification of the resulting states; completeness itself
is proved by the generic join-registry theorem. -/
noncomputable def ofWordRegistry
    (T : GeneratedSixteenTopData)
    {c : ℕ}
    {representative : Fin c → T.sourceStabilizer}
    (cover : FiniteConjugacyCardinalCover representative)
    {ι κ State Row : Type}
    (ambient : ι → T.sourceStabilizer)
    (stateGenerators : State → κ → T.sourceStabilizer)
    (registry : FiniteNormalJoinWordRegistryData
      cover ambient stateGenerators)
    (data : Row → GeneratedSixteenRowData T)
    (classify : ∀ s,
      (∃ r, Subgroup.closure (Set.range (stateGenerators s)) =
        (data r).sourceLocalMap.ker) ∨
      ((Subgroup.closure (Set.range (stateGenerators s))).index ≠ 3 ∧
        (Subgroup.closure (Set.range (stateGenerators s))).index ≠ 6) ∨
      ((Subgroup.closure (Set.range (stateGenerators s))).index = 6 ∧
        ∃ _normal :
          (Subgroup.closure (Set.range (stateGenerators s))).Normal,
          IsMulCommutative
            (T.sourceStabilizer ⧸
              Subgroup.closure (Set.range (stateGenerators s))))) :
    GeneratedSixteenSourceLocalNormalTable T where
  Row := Row
  data := data
  State := State
  state s := Subgroup.closure (Set.range (stateGenerators s))
  complete N := registry.complete N
  classify := classify

/-- Turn the source-stabilizer registry into the dependent top table used by
the generic literal transport.  Equality of kernels reconstructs the exact
target equivalence, so no row is selected by order alone. -/
noncomputable def toTopTable
    (T : GeneratedSixteenTopData) (C : GeneratedSixteenSourceLocalNormalTable T) :
    GeneratedSixteenTopTable T where
  Row := C.Row
  data := C.data
  complete := by
    intro L _ _ f hf hcard
    let f0 : T.sourceStabilizer →* L :=
      f.comp T.sourceStabilizerEquivLiteral.toMonoidHom
    have hf0 : Function.Surjective f0 :=
      hf.comp T.sourceStabilizerEquivLiteral.surjective
    obtain ⟨s, hs⟩ := C.complete f0.ker
    have hindex : f0.ker.index = Nat.card L := by
      rw [Subgroup.index_ker, f0.range_eq_top_of_surjective hf0,
        Nat.card_congr Subgroup.topEquiv.toEquiv]
    have hstateIndex : (C.state s).index = Nat.card L := by
      rw [hs]
      exact hindex
    rcases C.classify s with hrow | hout | hcomm
    · obtain ⟨r, hr⟩ := hrow
      have hkernels : f0.ker = (C.data r).sourceLocalMap.ker :=
        hs.symm.trans hr
      let e : L ≃* (C.data r).LocalTarget :=
        surjectiveTargetEquivOfKernelEq f0 (C.data r).sourceLocalMap
          hf0 (C.data r).sourceLocalMap_surjective hkernels
      have he0 : e.toMonoidHom.comp f0 = (C.data r).sourceLocalMap :=
        surjectiveTargetEquivOfKernelEq_comp f0
          (C.data r).sourceLocalMap hf0
          (C.data r).sourceLocalMap_surjective hkernels
      refine ⟨r, e, ?_⟩
      ext x
      have hx := DFunLike.congr_fun he0
        (T.sourceStabilizerEquivLiteral.symm x)
      simpa [f0, GeneratedSixteenRowData.literalLocalMap] using hx
    · rcases hout with ⟨hthree, hsix⟩
      rcases hcard with hL | ⟨hL, _⟩
      · exact False.elim (hthree (hstateIndex.trans hL))
      · exact False.elim (hsix (hstateIndex.trans hL))
    · rcases hcomm with ⟨hsix, hnormal, hcomm⟩
      rcases hcard with hL | ⟨hL, hnoncomm⟩
      · omega
      · apply False.elim
        apply hnoncomm
        letI : (C.state s).Normal := hnormal
        let e : (T.sourceStabilizer ⧸ C.state s) ≃* L :=
          (QuotientGroup.quotientMulEquivOfEq hs).trans
            (QuotientGroup.quotientKerEquivOfSurjective f0 hf0)
        refine ⟨⟨fun x y => ?_⟩⟩
        obtain ⟨a, rfl⟩ := e.surjective x
        obtain ⟨b, rfl⟩ := e.surjective y
        rw [← map_mul, hcomm.is_comm.comm a b, map_mul]

end GeneratedSixteenSourceLocalNormalTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
