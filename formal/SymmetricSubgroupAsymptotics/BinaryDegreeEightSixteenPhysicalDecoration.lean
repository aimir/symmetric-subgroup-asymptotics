import SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalDecoration
import SymmetricSubgroupAsymptotics.BinaryDegree16CarrierRouting

/-!
# One bounded decoration for changed degree-eight and degree-sixteen blocks

The degree-eight physical decoration uses eleven alphabet symbols per changed
block.  A degree-sixteen block uses eighteen payload symbols: its least
ambient point, one of the two carrier-route tags, and its sixteen labelled
point representatives.  We put both records in one robust format consisting
of one degree discriminator followed by an eighteen-symbol payload.

Thus a mixed record has length nineteen.  Every changed block is charged to
one coordinate of positive old support, so there are at most `Cold` records.
The standard decoration with `K = 10` has `20 * Cold` symbols and therefore
contains the complete mixed table.  The extra symbol per record avoids any
variable-length parsing convention.

Only finite reconstruction data are encoded here.  In particular the proper
nonabelian `16T1086` carrier itself remains literal in the transported word;
the record stores its route tag and point chart, not a product replacement.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierDecorationCode
open BinaryDegreeEightPhysicalDecoration

abbrev Alphabet := BinaryDegreeEightPhysicalDecoration.Alphabet

/-! ## The two degree-sixteen routes -/

inductive Degree16RouteTag
  | t1086
  | t1332
  deriving DecidableEq, Fintype

/-- The two-valued tag records exactly which of the checked degree-sixteen
carrier routes is used. -/
def MatchesCarrierOwnerRouteTag
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (O : BinaryDegree16SplitAnalyticClosure.CarrierOwner U M) :
    Degree16RouteTag → Prop
  | .t1086 =>
      ∃ g hg owner physical,
        O = .t1086 g hg owner physical
  | .t1332 =>
      ∃ g hg row physical,
        O = .t1332 g hg row physical

theorem exists_carrierOwnerRouteTag
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (O : BinaryDegree16SplitAnalyticClosure.CarrierOwner U M) :
    ∃ tag, MatchesCarrierOwnerRouteTag O tag := by
  cases O with
  | t1086 g hg owner physical =>
      exact ⟨.t1086,⟨g,hg,owner,physical,rfl⟩⟩
  | t1332 g hg row physical =>
      exact ⟨.t1332,⟨g,hg,row,physical,rfl⟩⟩

noncomputable def carrierOwnerRouteTag
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (O : BinaryDegree16SplitAnalyticClosure.CarrierOwner U M) :
    Degree16RouteTag :=
  Classical.choose (exists_carrierOwnerRouteTag O)

theorem carrierOwnerRouteTag_matches
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (O : BinaryDegree16SplitAnalyticClosure.CarrierOwner U M) :
    MatchesCarrierOwnerRouteTag O (carrierOwnerRouteTag O) :=
  Classical.choose_spec (exists_carrierOwnerRouteTag O)

def degree16RouteDigit : Degree16RouteTag → Fin 2
  | .t1086 => 0
  | .t1332 => 1

theorem degree16RouteDigit_injective :
    Function.Injective degree16RouteDigit := by
  intro a b h
  cases a <;> cases b <;> simp_all [degree16RouteDigit]

def degree16RouteSymbol (N : ℕ) : Degree16RouteTag → Alphabet N :=
  Fin.castLE (by omega) ∘ degree16RouteDigit

theorem degree16RouteSymbol_injective (N : ℕ) :
    Function.Injective (degree16RouteSymbol N) :=
  (Fin.castLE_injective _).comp degree16RouteDigit_injective

/-! ## The eighteen-symbol degree-sixteen record -/

structure Degree16BlockRecord (N : ℕ) where
  leastPoint : Fin (2 * N)
  route : Degree16RouteTag
  targetRepresentative : Fin 16 → Fin (2 * N)
  deriving Fintype

abbrev Degree16FieldShape := Fin 1 ⊕ (Fin 1 ⊕ Fin 16)

def degree16FieldEquiv : Degree16FieldShape ≃ Fin 18 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv

def Degree16BlockRecord.encode {N : ℕ} (r : Degree16BlockRecord N) :
    Fin 18 → Alphabet N := fun j ↦
  match degree16FieldEquiv.symm j with
  | .inl _ => pointSymbol N r.leastPoint
  | .inr (.inl _) => degree16RouteSymbol N r.route
  | .inr (.inr k) => pointSymbol N (r.targetRepresentative k)

theorem Degree16BlockRecord.encode_injective {N : ℕ} :
    Function.Injective (Degree16BlockRecord.encode (N := N)) := by
  intro r s hrs
  have hleast : r.leastPoint = s.leastPoint := by
    apply pointSymbol_injective N
    simpa [Degree16BlockRecord.encode] using
      congrFun hrs (degree16FieldEquiv (.inl 0))
  have hroute : r.route = s.route := by
    apply degree16RouteSymbol_injective N
    simpa [Degree16BlockRecord.encode] using
      congrFun hrs (degree16FieldEquiv (.inr (.inl 0)))
  have hrepresentatives :
      r.targetRepresentative = s.targetRepresentative := by
    funext k
    apply pointSymbol_injective N
    simpa [Degree16BlockRecord.encode] using
      congrFun hrs (degree16FieldEquiv (.inr (.inr k)))
  cases r
  cases s
  simp_all

variable {N : ℕ} (H : Subgroup (Equiv.Perm (Fin (2 * N))))

abbrev SixteenOrbit :=
  {o : Orbit H // Nat.card o.orbit = 16}

noncomputable instance sixteenOrbitFintype : Fintype (SixteenOrbit H) :=
  Fintype.ofFinite _

def sixteenOrbitLeast (o : SixteenOrbit H) : Fin (2 * N) :=
  orbitLeast H o.1

theorem sixteenOrbitLeast_injective :
    Function.Injective (sixteenOrbitLeast H) := by
  intro o p hop
  exact Subtype.ext (orbitLeast_injective H hop)

/-- Semantic source of one degree-sixteen record. -/
structure ChangedDegree16Block where
  orbit : SixteenOrbit H
  route : Degree16RouteTag
  chart : Fin 16 ≃ orbit.1.orbit

def ChangedDegree16Block.toRecord (B : ChangedDegree16Block H) :
    Degree16BlockRecord N where
  leastPoint := sixteenOrbitLeast H B.orbit
  route := B.route
  targetRepresentative := fun i ↦ (B.chart i).1

theorem ChangedDegree16Block.representative_mem
    (B : ChangedDegree16Block H) (i : Fin 16) :
    B.toRecord.targetRepresentative i ∈ B.orbit.1.orbit :=
  (B.chart i).2

theorem ChangedDegree16Block.representative_injective
    (B : ChangedDegree16Block H) :
    Function.Injective B.toRecord.targetRepresentative := by
  intro i j hij
  apply B.chart.injective
  exact Subtype.ext hij

/-! ## A uniform nineteen-symbol mixed record -/

inductive MixedBlockRecord (N : ℕ)
  | degree8 (record : BinaryDegreeEightPhysicalDecoration.BlockRecord N)
  | degree16 (record : Degree16BlockRecord N)
  deriving Fintype

def MixedBlockRecord.leastPoint {N : ℕ} : MixedBlockRecord N → Fin (2 * N)
  | .degree8 r => r.leastPoint
  | .degree16 r => r.leastPoint

def blockKindSymbol (N : ℕ) : Fin 2 → Alphabet N :=
  Fin.castLE (by omega)

theorem blockKindSymbol_injective (N : ℕ) :
    Function.Injective (blockKindSymbol N) :=
  Fin.castLE_injective _

/-- Embed the existing eleven degree-eight fields into the eighteen-symbol
payload, padding its last seven fields. -/
def degree8Payload {N : ℕ} (hN : 4 ≤ N)
    (r : BinaryDegreeEightPhysicalDecoration.BlockRecord N) :
    Fin 18 → Alphabet N := fun j ↦
  if hj : j.val < 11 then
    r.encode hN ⟨j.val,hj⟩
  else
    paddingSymbol N

abbrev MixedFieldShape := Fin 1 ⊕ Fin 18

def mixedFieldEquiv : MixedFieldShape ≃ Fin 19 := finSumFinEquiv

def MixedBlockRecord.encode {N : ℕ} (hN : 4 ≤ N) :
    MixedBlockRecord N → Fin 19 → Alphabet N
  | .degree8 r, j =>
      match mixedFieldEquiv.symm j with
      | .inl _ => blockKindSymbol N 0
      | .inr k => degree8Payload hN r k
  | .degree16 r, j =>
      match mixedFieldEquiv.symm j with
      | .inl _ => blockKindSymbol N 1
      | .inr k => r.encode k

theorem MixedBlockRecord.encode_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (MixedBlockRecord.encode hN) := by
  intro r s hrs
  cases r with
  | degree8 r =>
      cases s with
      | degree8 s =>
          apply congrArg MixedBlockRecord.degree8
          apply BinaryDegreeEightPhysicalDecoration.BlockRecord.encode_injective hN
          funext f
          let k : Fin 18 := Fin.castLE (by omega) f
          have hk : k.val < 11 := by simpa [k] using f.isLt
          have hf := congrFun hrs (mixedFieldEquiv (.inr k))
          simpa [MixedBlockRecord.encode,degree8Payload,hk] using hf
      | degree16 s =>
          have hhead := congrFun hrs (mixedFieldEquiv (.inl 0))
          have hbad : (0 : Fin 2) = 1 := by
            apply blockKindSymbol_injective N
            simpa [MixedBlockRecord.encode] using hhead
          norm_num at hbad
  | degree16 r =>
      cases s with
      | degree8 s =>
          have hhead := congrFun hrs (mixedFieldEquiv (.inl 0))
          have hbad : (1 : Fin 2) = 0 := by
            apply blockKindSymbol_injective N
            simpa [MixedBlockRecord.encode] using hhead
          norm_num at hbad
      | degree16 s =>
          apply congrArg MixedBlockRecord.degree16
          apply Degree16BlockRecord.encode_injective
          funext f
          simpa [MixedBlockRecord.encode] using
            congrFun hrs (mixedFieldEquiv (.inr f))

/-- `none` is represented by the old padding sentinel in all fields.  Every
actual record has a small degree discriminator in its first field. -/
def optionalMixedBlockEncode {N : ℕ} (hN : 4 ≤ N) :
    Option (MixedBlockRecord N) → Fin 19 → Alphabet N
  | none => fun _ ↦ paddingSymbol N
  | some r => r.encode hN

theorem optionalMixedBlockEncode_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (optionalMixedBlockEncode hN) := by
  intro r s hrs
  cases r with
  | none =>
      cases s with
      | none => rfl
      | some s =>
          exfalso
          have hhead := congrArg Fin.val
            (congrFun hrs (mixedFieldEquiv (.inl 0)))
          cases s <;>
            simp [optionalMixedBlockEncode,MixedBlockRecord.encode,
              paddingSymbol,blockKindSymbol] at hhead <;> omega
  | some r =>
      cases s with
      | none =>
          exfalso
          have hhead := congrArg Fin.val
            (congrFun hrs (mixedFieldEquiv (.inl 0)))
          cases r <;>
            simp [optionalMixedBlockEncode,MixedBlockRecord.encode,
              paddingSymbol,blockKindSymbol] at hhead <;> omega
      | some s =>
          exact congrArg some (MixedBlockRecord.encode_injective hN hrs)

/-! ## Packing and the explicit constant `K = 10` -/

abbrev MixedBlockTable (N Cold : ℕ) :=
  Fin Cold → Option (MixedBlockRecord N)

def IsCanonical {N Cold : ℕ} (T : MixedBlockTable N Cold) : Prop :=
  ∃ count : ℕ, count ≤ Cold ∧
    (∀ i : Fin Cold, (T i).isSome ↔ i.val < count) ∧
    ∀ (i j : Fin Cold) (ri rj : MixedBlockRecord N),
      T i = some ri → T j = some rj → i < j →
        ri.leastPoint < rj.leastPoint

abbrev CanonicalMixedBlockTable (N Cold : ℕ) :=
  {T : MixedBlockTable N Cold // IsCanonical T}

/-- Nineteen fields per block fit into the twenty positions supplied per old
support unit by `K = 10`. -/
def packMixedTable {N Cold : ℕ} (hN : 4 ≤ N)
    (T : MixedBlockTable N Cold) : DecorationCode N Cold 10 := fun z ↦
  if hz : z.val < Cold * 19 then
    let q : Fin (Cold * 19) := ⟨z.val,hz⟩
    let bf : Fin Cold × Fin 19 := finProdFinEquiv.symm q
    optionalMixedBlockEncode hN (T bf.1) bf.2
  else
    paddingSymbol N

theorem packMixedTable_injective {N Cold : ℕ} (hN : 4 ≤ N) :
    Function.Injective (packMixedTable (Cold := Cold) hN) := by
  intro T U hTU
  funext b
  apply optionalMixedBlockEncode_injective hN
  funext f
  let q : Fin (Cold * 19) := finProdFinEquiv (b,f)
  let z : Fin (10 * (2 * Cold)) := Fin.castLE (by omega) q
  have hz : z.val < Cold * 19 := by simpa [z] using q.isLt
  have hfield := congrFun hTU z
  have hbf : finProdFinEquiv.symm q = (b,f) :=
    finProdFinEquiv.symm_apply_apply (b,f)
  unfold packMixedTable at hfield
  simp only [dif_pos hz] at hfield
  change optionalMixedBlockEncode hN
      (T (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2 =
    optionalMixedBlockEncode hN
      (U (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2 at hfield
  simpa [hbf] using hfield

theorem mixedDecoration_symbol_length (N Cold : ℕ) :
    10 * (2 * Cold) = 20 * Cold := by omega

theorem mixedRecord_fields_fit (Cold : ℕ) :
    19 * Cold ≤ 10 * (2 * Cold) := by omega

theorem canonicalMixedPack_injective {N Cold : ℕ} (hN : 4 ≤ N) :
    Function.Injective
      (fun T : CanonicalMixedBlockTable N Cold ↦
        packMixedTable hN T.1) := by
  intro T U h
  exact Subtype.ext (packMixedTable_injective hN h)

theorem canonicalMixedTable_card_le_decoration
    {N Cold : ℕ} (hN : 4 ≤ N) :
    Nat.card (CanonicalMixedBlockTable N Cold) ≤
      Nat.card (DecorationCode N Cold 10) :=
  Nat.card_le_card_of_injective _ (canonicalMixedPack_injective hN)

/-- Old-support charging is shared by degree-eight and degree-sixteen changed
coordinates: their union is a subtype of the positive-old-support indices,
whose cardinality is at most `Cold`. -/
theorem mixedChangedCoordinate_card_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (slot : ι → BinaryCarrierWordClosure.Slot) {Cold : ℕ}
    (R : Retention slot Cold) :
    Nat.card {i : ι // 0 < R.oldSupport i} ≤ Cold :=
  positiveOldSupport_card_le slot R

/-- The exact numerical budget used by the mixed physical source code. -/
theorem mixedDecoration_card_le {N Cold : ℕ} (hN : 4 ≤ N) :
    Nat.card (CanonicalMixedBlockTable N Cold) ≤
      (2 * N + 2) ^ (10 * (2 * Cold)) := by
  calc
    Nat.card (CanonicalMixedBlockTable N Cold) ≤
        Nat.card (DecorationCode N Cold 10) :=
      canonicalMixedTable_card_le_decoration hN
    _ = (2 * N + 2) ^ (10 * (2 * Cold)) :=
      decorationCode_card N Cold 10

end SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration
