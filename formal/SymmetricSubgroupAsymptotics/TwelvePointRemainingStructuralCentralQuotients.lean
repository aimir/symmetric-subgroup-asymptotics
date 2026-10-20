import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.PrimeCentralSocleRelativeHead
import SymmetricSubgroupAsymptotics.BinaryCharacterProducts
import SymmetricSubgroupAsymptotics.BinaryCentralOmegaDetection

/-! The central rank in each original quotient follows from the original
normal relative heads. All central binary directions are retained, not only
central minimal factors of a selected noncentral socle predicate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
local instance centralQuotients_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G : Type} [Group G] [Finite G]

theorem central_vector_quotient_finrank_le_allRelativeHeads
    (r : ℕ) (hhead : ∀ (M : Subgroup G) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ r)
    (N : Subgroup G) [N.Normal]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : Multiplicative V →* G ⧸ N) (hf : Function.Injective f)
    (hcentral : f.range ≤ Subgroup.center (G ⧸ N)) :
    Module.finrank (ZMod 2) V ≤ r := by
  let q := QuotientGroup.mk' N
  let H := f.range
  letI : H.Normal := by
    constructor
    intro x hx g
    have hc : g*x = x*g := Subgroup.mem_center_iff.mp (hcentral hx) g
    have he : g*x*g⁻¹=x := by rw [hc]; group
    rw [he]
    exact hx
  let K := H.comap q
  letI : K.Normal := Subgroup.Normal.comap inferInstance q
  have hNK : N ≤ K := by
    intro n hn
    change q n ∈ H
    rw [show q n=1 from (QuotientGroup.eq_one_iff (N := N) n).mpr hn]
    exact H.one_mem
  have hquot : normalChainQuotient N K=H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) H
  have hh := primeRelativeHead_normalChainQuotient_le 2 N K hNK
  let eid : (G ⧸ N) ≃* (G ⧸ N) := MulEquiv.refl _
  have hmap : (normalChainQuotient N K).map eid.toMonoidHom = H := by
    change (normalChainQuotient N K).map (MonoidHom.id _) = H
    rw [Subgroup.map_id]
    exact hquot
  have hH : Module.finrank (ZMod 2) (primeRelativeCharacters 2 H) ≤ r :=
    (relativeCharacterAmbientCongr 2 eid (normalChainQuotient N K) H hmap).finrank_eq.le.trans
      (hh.trans (hhead K))
  have hc : Module.finrank (ZMod 2) (PrimeCharacters 2 H) ≤ r := by
    rw [← (primeRelativeCharactersEquivPrimeCharactersOfCentral 2 H hcentral).finrank_eq]
    exact hH
  let e : Multiplicative V ≃* H := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have he := primeCharacter_finrank_congr 2 e
  change binaryCharacterRank (Multiplicative V) = _ at he
  rw [binaryCharacterRank_multiplicative] at he
  exact he.le.trans hc

theorem centralOmega_quotient_finrank_le_allRelativeHeads
    (r : ℕ) (hhead : ∀ (M : Subgroup G) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ r)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega (G ⧸ N))) ≤ r := by
  let f : Multiplicative (Additive (binaryCentralOmega (G ⧸ N))) →* G ⧸ N := {
    toFun z := binaryCentralOmegaEmbedding z.toAdd.toMul
    map_one' := map_one binaryCentralOmegaEmbedding
    map_mul' _ _ := map_mul binaryCentralOmegaEmbedding _ _ }
  apply central_vector_quotient_finrank_le_allRelativeHeads r hhead N f
    (binaryCentralOmegaEmbedding_injective.comp
      (Additive.toMul.injective.comp Multiplicative.toAdd.injective))
  rintro _ ⟨z,rfl⟩
  exact z.toAdd.toMul.val.property

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
