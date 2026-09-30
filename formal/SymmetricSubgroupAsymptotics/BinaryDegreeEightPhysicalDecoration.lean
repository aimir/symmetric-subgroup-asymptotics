import SymmetricSubgroupAsymptotics.BinaryCarrierDecorationCode
import SymmetricSubgroupAsymptotics.BinaryCarrierDependentVariableWordProducer
import SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge
import Mathlib.Data.Fintype.Sort

/-!
# Bounded physical decorations for varying degree-eight carrier cells

This file isolates the finite information which may vary from one actual
labelled degree-eight carrier residual to another.  It does not require all
sources to lie in one fixed product cell.

A changed degree-eight block is recorded by eleven alphabet symbols:

* its least ambient point (one symbol), which also canonically orders the
  changed blocks;
* a two-symbol local carrier-route tag (eight base routes or three exceptional
  routes); and
* the eight ambient target representatives of its local point chart.

The two extra letters in the alphabet `Fin (2*N+2)` supply a padding sentinel.
Consequently at most `Cold` changed blocks fit injectively in
`DecorationCode N Cold 6`: eleven symbols per block fit in its `12*Cold`
positions.  The last section packages the only remaining physical obligation:
construct the target subgroup and prove that it and this block table recover
the original subgroup.  Once that is supplied, the checked abstract transport
is obtained directly, without a global fixed product chart.

No assertion about non-eight-point orbits is made here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalDecoration

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryCarrierDecorationCode
open BinaryCarrierDependentVariableWordProducer
open BinaryDegreeEightBaseRoutes
open BinaryDegreeEightPhysicalAnalyticClosure

/-! ## Least-point order on literal orbits -/

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

abbrev Orbit := OrbitProfileFromOrbits.Orbit H

def orbitPointFinset (o : Orbit H) : Finset (Fin n) :=
  Finset.univ.filter (fun x ↦ x ∈ o.orbit)

theorem orbitPointFinset_nonempty (o : Orbit H) :
    (orbitPointFinset H o).Nonempty := by
  refine ⟨o.out, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [o.orbit_eq_orbit_out Quotient.out_eq']
  exact MulAction.mem_orbit_self o.out

/-- The least labelled point of an actual orbit. -/
def orbitLeast (o : Orbit H) : Fin n :=
  (orbitPointFinset H o).min' (orbitPointFinset_nonempty H o)

theorem orbitLeast_mem (o : Orbit H) : orbitLeast H o ∈ o.orbit :=
  (Finset.mem_filter.mp
    (Finset.min'_mem (orbitPointFinset H o)
      (orbitPointFinset_nonempty H o))).2

/-- Distinct literal orbits have distinct least points. -/
theorem orbitLeast_injective : Function.Injective (orbitLeast H) := by
  intro o p hop
  calc
    o = Quotient.mk (MulAction.orbitRel H (Fin n)) (orbitLeast H o) :=
      (MulAction.orbitRel.Quotient.mem_orbit.mp (orbitLeast_mem H o)).symm
    _ = Quotient.mk (MulAction.orbitRel H (Fin n)) (orbitLeast H p) :=
      congrArg (Quotient.mk (MulAction.orbitRel H (Fin n))) hop
    _ = p := MulAction.orbitRel.Quotient.mem_orbit.mp (orbitLeast_mem H p)

/-- The literal eight-point orbit quotient. -/
abbrev EightOrbit := {o : Orbit H // Nat.card o.orbit = 8}

noncomputable instance eightOrbitFintype : Fintype (EightOrbit H) :=
  Fintype.ofFinite _

def eightOrbitLeast (o : EightOrbit H) : Fin n := orbitLeast H o.1

theorem eightOrbitLeast_injective : Function.Injective (eightOrbitLeast H) := by
  intro o p hop
  exact Subtype.ext (orbitLeast_injective H hop)

/-! ## The eleven-symbol local record -/

/-- The finite carrier choice retained on a changed degree-eight block.  In
the exceptional branch the action index is determined by the selected checked
chart, so the three-valued exceptional tag is sufficient. -/
inductive LocalRouteTag
  | base (b : Base)
  | exceptional (e : Fin 3)
  deriving DecidableEq, Fintype

/-- Proposition-valued relation between an owner proof and its finite branch.
`CarrierOwner` is a proposition, so its witness is converted to data only
through classical choice after existence has been proved in `Prop`. -/
def MatchesOwnerRouteTag
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal] (_O : CarrierOwner U M)
    (tag : LocalRouteTag) : Prop :=
  (∃ (b : Base) (g : Equiv.Perm (Fin 8))
      (hg : relabelSubgroup g U =
        BinaryActionRegistry8.actions (baseIndex b)),
      tag = .base b) ∨
  ∃ (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : relabelSubgroup g U = BinaryActionRegistry8.actions i)
      (e : Fin 3)
      (source : (binaryEightTransportChart e).source =
        BinaryActionRegistry8.actions i)
      (_axis : (binaryEightTransportChart e).axis =
        (actionConjugacyNormal g hg M).map
          (BinaryActionRegistry8.actions i).subtype),
      tag = .exceptional e

theorem exists_ownerRouteTag
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal] (O : CarrierOwner U M) :
    ∃ tag, MatchesOwnerRouteTag O tag := by
  cases O with
  | base b g hg => exact ⟨.base b,Or.inl ⟨b,g,hg,rfl⟩⟩
  | exceptional i g hg e source axis =>
      exact ⟨.exceptional e,Or.inr ⟨i,g,hg,e,source,axis,rfl⟩⟩

/-- The canonically chosen finite owner branch. -/
noncomputable def ownerRouteTag
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal] (O : CarrierOwner U M) : LocalRouteTag :=
  Classical.choose (exists_ownerRouteTag O)

theorem ownerRouteTag_matches
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal] (O : CarrierOwner U M) :
    MatchesOwnerRouteTag O (ownerRouteTag O) :=
  Classical.choose_spec (exists_ownerRouteTag O)

/-- A fixed injective numbering of the eight base routes. -/
def baseDigit : Base → Fin 8
  | .t18 => 0
  | .e8 => 1
  | .t26 => 2
  | .t27 => 3
  | .t28 => 4
  | .t29 => 5
  | .t31 => 6
  | .t35 => 7

theorem baseDigit_injective : Function.Injective baseDigit := by
  intro b c h
  fin_cases b <;> fin_cases c <;> simp_all [baseDigit]

abbrev Alphabet (N : ℕ) := Fin (2 * N + 2)

/-- Ambient points occupy the first `2*N` alphabet letters. -/
def pointSymbol (N : ℕ) : Fin (2 * N) → Alphabet N :=
  Fin.castLE (by omega)

theorem pointSymbol_injective (N : ℕ) :
    Function.Injective (pointSymbol N) :=
  Fin.castLE_injective _

def smallDigit {N : ℕ} (hN : 4 ≤ N) : Fin 8 → Alphabet N :=
  Fin.castLE (by omega)

theorem smallDigit_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (smallDigit hN) :=
  Fin.castLE_injective _

/-- Two alphabet letters encode all eleven local route tags.  The first
letter separates base and exceptional routes and the second is the local
index. -/
def routeHeader {N : ℕ} (hN : 4 ≤ N) :
    LocalRouteTag → Fin 2 → Alphabet N
  | .base b =>
      Fin.cases (smallDigit hN 0) (fun _ ↦ smallDigit hN (baseDigit b))
  | .exceptional e =>
      Fin.cases (smallDigit hN 1)
        (fun _ ↦ smallDigit hN (Fin.castLE (by omega) e))

theorem routeHeader_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (routeHeader hN) := by
  intro a b hab
  have hzero := congrFun hab (0 : Fin 2)
  have hone := congrFun hab (1 : Fin 2)
  cases a with
  | base a =>
      cases b with
      | base b =>
          apply congrArg LocalRouteTag.base
          apply baseDigit_injective
          apply smallDigit_injective hN
          simpa [routeHeader] using hone
      | exceptional b =>
          have hbad : (0 : Fin 8) = 1 := by
            apply smallDigit_injective hN
            simpa [routeHeader] using hzero
          norm_num at hbad
  | exceptional a =>
      cases b with
      | base b =>
          have hbad : (1 : Fin 8) = 0 := by
            apply smallDigit_injective hN
            simpa [routeHeader] using hzero
          norm_num at hbad
      | exceptional b =>
          apply congrArg LocalRouteTag.exceptional
          apply Fin.castLE_injective (show 3 ≤ 8 by omega)
          apply smallDigit_injective hN
          simpa [routeHeader] using hone

/-- The reconstruction data for one changed block.  The eight representatives
record the complete labelled point chart, rather than only its unlabelled
image set. -/
structure BlockRecord (N : ℕ) where
  leastPoint : Fin (2 * N)
  route : LocalRouteTag
  targetRepresentative : Fin 8 → Fin (2 * N)
  deriving Fintype

/-- Semantic source of a block record on an actual labelled permutation
subgroup.  The equivalence records all eight target representatives, so its
image is exactly the literal orbit. -/
structure ChangedBlock {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N)))) where
  orbit : EightOrbit H
  route : LocalRouteTag
  chart : Fin 8 ≃ orbit.1.orbit

def ChangedBlock.toRecord {N : ℕ}
    {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedBlock H) : BlockRecord N where
  leastPoint := orbitLeast H B.orbit.1
  route := B.route
  targetRepresentative := fun i ↦ (B.chart i).1

theorem ChangedBlock.representative_mem {N : ℕ}
    {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedBlock H) (i : Fin 8) :
    (B.toRecord.targetRepresentative i) ∈ B.orbit.1.orbit :=
  (B.chart i).2

theorem ChangedBlock.representative_injective {N : ℕ}
    {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedBlock H) :
    Function.Injective B.toRecord.targetRepresentative := by
  intro i j hij
  apply B.chart.injective
  exact Subtype.ext hij

abbrev FieldShape := Fin 1 ⊕ (Fin 2 ⊕ Fin 8)

def fieldEquiv : FieldShape ≃ Fin 11 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv

/-- The literal eleven-symbol record: least point, two route letters, then
the eight target representatives. -/
def BlockRecord.encode {N : ℕ} (hN : 4 ≤ N) (r : BlockRecord N) :
    Fin 11 → Alphabet N := fun j ↦
  match fieldEquiv.symm j with
  | .inl _ => pointSymbol N r.leastPoint
  | .inr (.inl k) => routeHeader hN r.route k
  | .inr (.inr k) => pointSymbol N (r.targetRepresentative k)

theorem BlockRecord.encode_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (BlockRecord.encode hN) := by
  intro r s hrs
  have hleast : r.leastPoint = s.leastPoint := by
    apply pointSymbol_injective N
    simpa [BlockRecord.encode] using
      congrFun hrs (fieldEquiv (.inl 0))
  have hroute : r.route = s.route := by
    apply routeHeader_injective hN
    funext k
    simpa [BlockRecord.encode] using
      congrFun hrs (fieldEquiv (.inr (.inl k)))
  have hrepresentatives :
      r.targetRepresentative = s.targetRepresentative := by
    funext k
    apply pointSymbol_injective N
    simpa [BlockRecord.encode] using
      congrFun hrs (fieldEquiv (.inr (.inr k)))
  cases r
  cases s
  simp_all

/-- The first alphabet letter not representing an ambient point. -/
def paddingSymbol (N : ℕ) : Alphabet N := ⟨2 * N, by omega⟩

/-- `none` pads an unused block position.  Its sentinel head distinguishes it
from every actual least point. -/
def optionalBlockEncode {N : ℕ} (hN : 4 ≤ N) :
    Option (BlockRecord N) → Fin 11 → Alphabet N
  | none => fun _ ↦ paddingSymbol N
  | some r => r.encode hN

theorem optionalBlockEncode_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (optionalBlockEncode hN) := by
  intro r s hrs
  cases r with
  | none =>
      cases s with
      | none => rfl
      | some s =>
          exfalso
          have hhead := congrArg Fin.val
            (congrFun hrs (fieldEquiv (.inl 0)))
          simp [optionalBlockEncode, BlockRecord.encode, paddingSymbol,
            pointSymbol] at hhead
          omega
  | some r =>
      cases s with
      | none =>
          exfalso
          have hhead := congrArg Fin.val
            (congrFun hrs (fieldEquiv (.inl 0)))
          simp [optionalBlockEncode, BlockRecord.encode, paddingSymbol,
            pointSymbol] at hhead
          omega
      | some s =>
          exact congrArg some (BlockRecord.encode_injective hN hrs)

/-! ## Packing at most `Cold` records into the standard decoration -/

abbrev BlockTable (N Cold : ℕ) := Fin Cold → Option (BlockRecord N)

/-- Canonical tables use an active prefix and order its changed blocks by
their least ambient points.  This is a property of the encoding, not an
additional mark attached to the counted subgroup. -/
def IsCanonical {N Cold : ℕ} (T : BlockTable N Cold) : Prop :=
  ∃ count : ℕ, count ≤ Cold ∧
    (∀ i : Fin Cold, (T i).isSome ↔ i.val < count) ∧
    ∀ (i j : Fin Cold) (ri rj : BlockRecord N),
      T i = some ri → T j = some rj → i < j →
        ri.leastPoint < rj.leastPoint

abbrev CanonicalBlockTable (N Cold : ℕ) :=
  {T : BlockTable N Cold // IsCanonical T}

/-- Eleven fields per block fit in the twelve positions supplied by `K=6`.
Unused positions are filled by the padding sentinel. -/
def packTable {N Cold : ℕ} (hN : 4 ≤ N) (T : BlockTable N Cold) :
    DecorationCode N Cold 6 := fun z ↦
  if hz : z.val < Cold * 11 then
    let q : Fin (Cold * 11) := ⟨z.val, hz⟩
    let bf : Fin Cold × Fin 11 := finProdFinEquiv.symm q
    optionalBlockEncode hN (T bf.1) bf.2
  else
    paddingSymbol N

theorem packTable_injective {N Cold : ℕ} (hN : 4 ≤ N) :
    Function.Injective (packTable (Cold := Cold) hN) := by
  intro T U hTU
  funext b
  apply optionalBlockEncode_injective hN
  funext f
  let q : Fin (Cold * 11) := finProdFinEquiv (b, f)
  let z : Fin (6 * (2 * Cold)) := Fin.castLE (by omega) q
  have hz : z.val < Cold * 11 := by
    simpa [z] using q.isLt
  have hfield := congrFun hTU z
  have hbf : finProdFinEquiv.symm q = (b,f) :=
    finProdFinEquiv.symm_apply_apply (b,f)
  unfold packTable at hfield
  simp only [dif_pos hz] at hfield
  change optionalBlockEncode hN
      (T (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2 =
    optionalBlockEncode hN
      (U (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2 at hfield
  simpa [hbf] using hfield

/-- The standard decoration itself is already the exact `12*Cold`-symbol
budget. -/
theorem packedTable_symbol_length (N Cold : ℕ) :
    6 * (2 * Cold) = 12 * Cold := by omega

/-- A canonical table inherits injectivity from its underlying padded table. -/
theorem canonicalPack_injective {N Cold : ℕ} (hN : 4 ≤ N) :
    Function.Injective
      (fun T : CanonicalBlockTable N Cold ↦ packTable hN T.1) := by
  intro T U h
  exact Subtype.ext (packTable_injective hN h)

/-! ## Charging changed blocks to old support -/

/-- Any set of coordinates with positive old support has cardinality at most
the complete old support.  This is the precise charging lemma needed before
putting changed blocks in the `Cold` table. -/
theorem positiveOldSupport_card_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (slot : ι → BinaryCarrierWordClosure.Slot) {Cold : ℕ}
    (R : Retention slot Cold) :
    Nat.card {i : ι // 0 < R.oldSupport i} ≤ Cold := by
  let f : {i : ι // 0 < R.oldSupport i} →
      Σ i : ι, Fin (R.oldSupport i) :=
    fun i ↦ ⟨i.1, ⟨0, i.2⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg Sigma.fst hij)
  calc
    Nat.card {i : ι // 0 < R.oldSupport i} ≤
        Nat.card (Σ i : ι, Fin (R.oldSupport i)) :=
      Nat.card_le_card_of_injective f hf
    _ = ∑ i : ι, R.oldSupport i := by
      rw [Nat.card_sigma]
      simp
    _ = Cold := R.old_sum

/-! ## Reconstruction and direct physical transport -/

/-- The dependent-word specialization.  Here the canonical block table
determines the complete heterogeneous routed word, including its coordinate
type, and a source object is reconstructed from that table and its dependent
word source.  This form uses the existing dependent-word
producer and therefore permits different subgroups to use different carrier
cells without summing a raw profile alphabet.  If unchanged axes still vary
inside one table fibre, use `PhysicalEncoding` below together with the
cross-variable axis-recovery lemmas instead. -/
structure DependentEncoding
    (Actual : Type*) (N Cold : ℕ) (hN : 4 ≤ N) where
  routedWord : CanonicalBlockTable N Cold → RoutedWord N Cold
  blocks : Actual → CanonicalBlockTable N Cold
  sourceAt : ∀ x : Actual, (routedWord (blocks x)).Source
  recover : (Σ d : CanonicalBlockTable N Cold, (routedWord d).Source) → Actual
  recover_encode : ∀ x, recover ⟨blocks x, sourceAt x⟩ = x

namespace DependentEncoding

variable {Actual : Type*} {N Cold : ℕ} {hN : 4 ≤ N}

def code (E : DependentEncoding Actual N Cold hN) :
    Actual → Σ d : CanonicalBlockTable N Cold, (E.routedWord d).Source :=
  fun x ↦ ⟨E.blocks x, E.sourceAt x⟩

theorem code_injective (E : DependentEncoding Actual N Cold hN) :
    Function.Injective E.code := by
  intro x y hxy
  calc
    x = E.recover (E.code x) := (E.recover_encode x).symm
    _ = E.recover (E.code y) := congrArg E.recover hxy
    _ = y := E.recover_encode y

/-- Install the canonical table as the decoration of the dependent variable
word producer.  Its cardinality is bounded by the explicit injection into
`DecorationCode N Cold 6`. -/
def toCode (E : DependentEncoding Actual N Cold hN) :
    BinaryCarrierDependentVariableWordProducer.Code Actual N Cold 6 where
  Decoration := CanonicalBlockTable N Cold
  decorationFinite := inferInstance
  routedWord := E.routedWord
  code := E.code
  code_injective := E.code_injective
  decoration_card_le := by
    calc
      Nat.card (CanonicalBlockTable N Cold) ≤
          Nat.card (DecorationCode N Cold 6) :=
        Nat.card_le_card_of_injective
          (fun T ↦ packTable hN T.1) (canonicalPack_injective hN)
      _ = (2 * N + 2) ^ (6 * (2 * Cold)) :=
        decorationCode_card N Cold 6

/-- The explicit block table therefore gives the exact retained-bin bound
for every finite actual family equipped with dependent-word reconstruction. -/
theorem card_le_bound_mul_sum [Finite Actual]
    (E : DependentEncoding Actual N Cold hN) :
    Nat.card Actual ≤
      (2 * N + 2) ^ (6 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  BinaryCarrierDependentVariableWordProducer.Code.card_le_bound_mul_sum
    E.toCode

end DependentEncoding

/-- A varying-cell producer.  `blocks` contains only the changed degree-eight
blocks.  The actual physical target retains all unchanged data, including
pure E8 blocks.  `recover` is therefore allowed to inspect both components.

This interface deliberately has no premise about non-eight-point orbits.  A
caller may use it on a source family only after those other orbits have been
handled by their own owners. -/
structure PhysicalEncoding
    (Actual : Type*) (N Cold : ℕ) (hN : 4 ≤ N) where
  blocks : Actual → CanonicalBlockTable N Cold
  target : Actual → Target N Cold
  recover : CanonicalBlockTable N Cold → Target N Cold → Actual
  recover_encode : ∀ x, recover (blocks x) (target x) = x

namespace PhysicalEncoding

variable {Actual : Type*} {N Cold : ℕ} {hN : 4 ≤ N}

def decoration (E : PhysicalEncoding Actual N Cold hN) (x : Actual) :
    DecorationCode N Cold 6 :=
  packTable hN (E.blocks x).1

/-- The packed decoration and physical target recover the actual source. -/
theorem decoration_target_injective
    (E : PhysicalEncoding Actual N Cold hN) :
    Function.Injective (fun x ↦ (E.decoration x, E.target x)) := by
  intro x y hxy
  have hdecoration : E.decoration x = E.decoration y := congrArg Prod.fst hxy
  have htarget : E.target x = E.target y := congrArg Prod.snd hxy
  have hblocks : E.blocks x = E.blocks y :=
    canonicalPack_injective hN hdecoration
  calc
    x = E.recover (E.blocks x) (E.target x) := (E.recover_encode x).symm
    _ = E.recover (E.blocks y) (E.target y) := by rw [hblocks, htarget]
    _ = y := E.recover_encode y

/-- The direct physical interface has the same exact cardinal consequence.
This statement is independent of how the target was constructed; the only
remaining physical obligation is `recover_encode`. -/
theorem card_le_bound_mul_sum [Finite Actual]
    (E : PhysicalEncoding Actual N Cold hN) :
    Nat.card Actual ≤
      (2 * N + 2) ^ (6 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  letI : Finite (DecorationCode N Cold 6) := inferInstance
  calc
    Nat.card Actual ≤
        Nat.card (DecorationCode N Cold 6 × Target N Cold) :=
      Nat.card_le_card_of_injective
        (fun x ↦ (E.decoration x,E.target x)) E.decoration_target_injective
    _ = Nat.card (DecorationCode N Cold 6) * Nat.card (Target N Cold) :=
      Nat.card_prod _ _
    _ = (2 * N + 2) ^ (6 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
      rw [decorationCode_card,Nat.card_sigma]

/-- A completed varying-cell encoding directly gives the abstract physical
transport.  No common product cell or fixed global route word occurs in this
construction. -/
def toTransport
    {Residual : Subgroup (Equiv.Perm (Fin (2 * N))) → Prop}
    (E : PhysicalEncoding (Source N Residual) N Cold hN) :
    Transport N Cold 6 Residual where
  Decoration := DecorationCode N Cold 6
  decorationFinite := inferInstance
  decoration := E.decoration
  target := E.target
  joint_injective := E.decoration_target_injective
  decoration_card_le := (decorationCode_card N Cold 6).le

end PhysicalEncoding

end SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalDecoration
