#!/usr/bin/env python3
"""Emit one small original relative-radical and character-coordinate pair.

Only the selected certified derived subgroup (at most64 rows) and its
relative radical (at most8 rows) are explored. No ambient group, normal
menu, compiler, GAP process, or network is used. Every emitted group fact
still requires Lean checking. --check is exact-byte, read-only replay.
Reports and exploratory data belong outside the publication repository.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import deque
import hashlib
import json
import re
from pathlib import Path
import time
import export_lean_derived_group_words as derived

square = derived.square
ROOT, OUT = square.ROOT, square.OUT
require = square.require
MAX_OPERATIONS, MAX_SECONDS, MAX_OUTPUT_BYTES = 100_000, 5.0, 131_072


def search(g, budget, max_radical_rows):
    D = derived.search(g, budget)
    b = [square.evaluate(w, g) for w in D['basis_words']]
    identity = tuple(range(16))
    def mul(a, c):
        budget.operation()
        return square.mul(a, c)
    def inv(a):
        budget.operation()
        return square.inv(a)
    def comm(a, c):
        return mul(mul(mul(a, c), inv(a)), inv(c))
    candidates, seeds = [], []
    rows, words, index = [identity], [[]], {identity: 0}
    def close():
        nonlocal rows, words, index
        rows, words, index = [identity], [[]], {identity: 0}
        queue = deque([0])
        while queue:
            i = queue.popleft()
            for j, c in enumerate(candidates):
                x = mul(rows[i], c)
                if x in index:
                    continue
                require(len(rows) < max_radical_rows, 'selected radical-row ceiling reached')
                require(len(words[i]) < 16, 'selected radical word ceiling reached')
                index[x] = len(rows)
                rows.append(x)
                words.append(words[i] + [j])
                queue.append(len(rows)-1)
    tests = [(('pow', j), mul(x, x)) for j, x in enumerate(b)]
    tests += [(('comm', j, i), comm(x, a)) for j, x in enumerate(b) for i, a in enumerate(g)]
    for seed, x in tests:
        if x not in index:
            require(len(candidates) < 8, 'candidate-generator ceiling reached')
            candidates.append(x)
            seeds.append(seed)
            close()
    require(candidates, 'nontrivial radical template required')
    require(all(x in D['rows'] for x in rows), 'candidate escapes actual derived rows')
    def locate(x):
        require(x in index, 'candidate does not cover a required original equation')
        return index[x]
    nxt = [[locate(mul(x, y)) for y in candidates] for x in rows]
    conjugates = [[locate(mul(mul(a, x), inv(a))) for x in candidates] for a in g]
    powers = [locate(mul(x, x)) for x in b]
    mixed = [[locate(comm(x, a)) for a in g] for x in b]
    coset = {x: min(mul(x, r) for r in rows) for x in D['rows']}
    coordinates, selected = {coset[identity]: 0}, []
    for j, x in enumerate(b):
        if coset[x] not in coordinates:
            bit = 1 << len(selected)
            selected.append(j)
            coordinates.update({coset[mul(key, x)]: v | bit for key, v in list(coordinates.items())})
    require(len(coordinates)*len(rows) == len(D['rows']), 'quotient coordinates do not cover D')
    require(1 <= len(selected) <= 4, 'character coordinate ceiling reached')
    qwords = [[i for i in range(len(selected)) if (coordinates[coset[x]] >> i) & 1] for x in b]
    residues = []
    for j, letters in enumerate(qwords):
        product = identity
        for i in letters:
            product = mul(product, b[selected[i]])
        residues.append(locate(mul(b[j], inv(product))))
    return dict(D=D, rows=rows, words=words, seeds=seeds, next=nxt,
                conjugates=conjugates, powers=powers, mixed=mixed,
                selected=selected, qwords=qwords, residues=residues,
                original_count=len(g), basis_count=len(b))


RADICAL = r'''import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalFiniteCertificate
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T@MASTER@

/-! Selected original relative-derived radical certificate. Its @ROWS@
rows are actual words in generator squares and mixed commutators. The
whole original ambient tuple is retained for every normality test. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T@MASTER@

abbrev Original := BinaryCarrierDerivedOrder16T@MASTER@.Original
abbrev D := commutator Original
private abbrev g := BinaryActionData16.node@MASTER@Generators
private abbrev words := BinaryCarrierDerivedOrder16T@MASTER@.basisWords
private abbrev ambient := closureGenerators g
private abbrev basis := derivedWordGenerators g words

def ambientBasis (j : Fin @BASIS@) : Equiv.Perm (Fin 16) := (words j).eval g
private def seed : Fin @CANDIDATES@ → Fin @BASIS@ ⊕ (Fin @BASIS@ × Fin @GENERATORS@) :=
  @SEEDS@
private def candidate (j : Fin @CANDIDATES@) : Original :=
  primeRelativeFiniteGenerators 2 ambient basis (seed j)
private def ambientCandidate (j : Fin @CANDIDATES@) : Equiv.Perm (Fin 16) :=
  primeRelativeFiniteGenerators 2 g ambientBasis (seed j)
private def rowWords : Fin @ROWS@ → List (Fin @CANDIDATES@) :=
  @WORDS@
def elements (i : Fin @ROWS@) : Original := ((rowWords i).map candidate).prod
def ambientRows (i : Fin @ROWS@) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map ambientCandidate).prod
private def next (i : Fin @ROWS@) (j : Fin @CANDIDATES@) : Fin @ROWS@ :=
  @NEXT@ i j
private def conjugateRow (i : Fin @GENERATORS@) (j : Fin @CANDIDATES@) : Fin @ROWS@ :=
  @CONJUGATES@ i j
private def powerRow : Fin @BASIS@ → Fin @ROWS@ := @POWERS@
private def mixedRow (j : Fin @BASIS@) (i : Fin @GENERATORS@) : Fin @ROWS@ :=
  @MIXED@ j i

theorem basis_coe (j : Fin @BASIS@) :
    (basis j : Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe g (words j)

private theorem candidate_coe (j : Fin @CANDIDATES@) :
    (candidate j : Equiv.Perm (Fin 16)) = ambientCandidate j := by
  cases hs : seed j with
  | inl k =>
    change ((primeRelativeFiniteGenerators 2 ambient basis (seed j) : Original) : Equiv.Perm (Fin 16)) = _
    simp only [hs, primeRelativeFiniteGenerators, Sum.elim_inl, ambientCandidate]
    change (basis k : Equiv.Perm (Fin 16)) ^ 2 = ambientBasis k ^ 2
    rw [basis_coe]
  | inr ki =>
    change ((primeRelativeFiniteGenerators 2 ambient basis (seed j) : Original) : Equiv.Perm (Fin 16)) = _
    simp only [hs, primeRelativeFiniteGenerators, Sum.elim_inr, ambientCandidate]
    change ⁅(basis ki.1 : Equiv.Perm (Fin 16)), g ki.2⁆ = ⁅ambientBasis ki.1, g ki.2⁆
    rw [basis_coe]

theorem elements_coe (i : Fin @ROWS@) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map candidate).prod) = _
  have hf : Original.subtype ∘ candidate = ambientCandidate := funext candidate_coe
  rw [map_list_prod, List.map_map, hf]
  rfl

private theorem next_pointwise : ∀ (i : Fin @ROWS@) (j : Fin @CANDIDATES@) (x : Fin 16),
    ambientRows (next i j) x = (ambientRows i * ambientCandidate j) x := by decide +kernel
private theorem conjugate_pointwise : ∀ (i : Fin @GENERATORS@) (j : Fin @CANDIDATES@) (x : Fin 16),
    ambientRows (conjugateRow i j) x = (g i * ambientCandidate j * (g i)⁻¹) x := by decide +kernel
private theorem power_pointwise : ∀ (j : Fin @BASIS@) (x : Fin 16),
    ambientRows (powerRow j) x = (ambientBasis j ^ 2) x := by decide +kernel
private theorem mixed_pointwise : ∀ (j : Fin @BASIS@) (i : Fin @GENERATORS@) (x : Fin 16),
    ambientRows (mixedRow j i) x = ⁅ambientBasis j, g i⁆ x := by decide +kernel
private theorem rows_injective_pointwise : ∀ (i j : Fin @ROWS@),
    (∀ x : Fin 16, ambientRows i x = ambientRows j x) → i = j := by decide +kernel

private def cayley : FiniteCayleyCertificate candidate @ROWS@ where
  elements := elements
  identity := 0
  identity_eq := rfl
  next := next
  next_eq := by
    intro i j
    apply Subtype.ext
    change (elements (next i j) : Equiv.Perm (Fin 16)) =
      (elements i : Equiv.Perm (Fin 16)) * (candidate j : Equiv.Perm (Fin 16))
    rw [elements_coe, elements_coe, candidate_coe]
    exact Equiv.ext (next_pointwise i j)
  words := rowWords
  words_eq _ := rfl

def certificate : PrimeRelativeRadicalFiniteCertificate 2 D ambient basis candidate @ROWS@ where
  cayley := cayley
  rows_injective := by
    intro i j h
    have he := congrArg Subtype.val h
    change (elements i : Equiv.Perm (Fin 16)) = (elements j : Equiv.Perm (Fin 16)) at he
    rw [elements_coe, elements_coe] at he
    exact rows_injective_pointwise i j (fun x => congrArg (fun f => f x) he)
  candidate_mem j := primeRelativeFiniteGenerators_mem 2 D ambient basis
    BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator (seed j)
  conjugateRow := conjugateRow
  conjugate_eq := by
    intro i j
    apply Subtype.ext
    change (elements (conjugateRow i j) : Equiv.Perm (Fin 16)) =
      g i * (candidate j : Equiv.Perm (Fin 16)) * (g i)⁻¹
    rw [elements_coe, candidate_coe]
    exact Equiv.ext (conjugate_pointwise i j)
  powerRow := powerRow
  power_eq := by
    intro j
    apply Subtype.ext
    change (elements (powerRow j) : Equiv.Perm (Fin 16)) = (basis j : Equiv.Perm (Fin 16)) ^ 2
    rw [elements_coe, basis_coe]
    exact Equiv.ext (power_pointwise j)
  mixedRow := mixedRow
  mixed_eq := by
    intro j i
    apply Subtype.ext
    change (elements (mixedRow j i) : Equiv.Perm (Fin 16)) =
      ⁅(basis j : Equiv.Perm (Fin 16)), g i⁆
    rw [elements_coe, basis_coe]
    exact Equiv.ext (mixed_pointwise j i)

theorem elements_mem_radical (i : Fin @ROWS@) : elements i ∈ primeRelativeRadical 2 D := by
  rw [← certificate.closure_eq_radical (closureGenerators_full g)
    BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator]
  exact (cayley.mem_closure_iff _).mpr ⟨i, rfl⟩

theorem card_relative_radical : Nat.card (primeRelativeRadical 2 D) = @ROWS@ :=
  certificate.card_radical (closureGenerators_full g)
    BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator

theorem relative_character_rank : Module.finrank (ZMod 2) (primeRelativeCharacters 2 D) = @RANK@ := by
  have h := primeRelativeRadical_card_factorization 2 D
  rw [BinaryCarrierDerivedOrder16T@MASTER@.card_commutator, card_relative_radical] at h
  have hp : 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 D) = 2 ^ @RANK@ := by omega
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hp

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T@MASTER@
'''

CHARACTERS = r'''import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterCoordinates
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T@MASTER@

/-! Complete coordinates on the actual whole-original-group invariant
derived characters. Every relation is certified modulo the original
relative radical on the original sixteen points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T@MASTER@

abbrev Original := BinaryCarrierDerivedOrder16T@MASTER@.Original
abbrev D := commutator Original
abbrev Characters := primeRelativeCharacters 2 D
private abbrev g := BinaryActionData16.node@MASTER@Generators
private abbrev words := BinaryCarrierDerivedOrder16T@MASTER@.basisWords
private abbrev basis := derivedWordGenerators g words

def originalBasis (j : Fin @BASIS@) : D :=
  ⟨basis j, (words j).eval_mem_commutator (closureGenerators g)⟩

theorem originalBasis_full : Subgroup.closure (Set.range originalBasis) = ⊤ := by
  apply Subgroup.map_injective D.subtype_injective
  rw [MonoidHom.map_closure]
  have himage : D.subtype '' Set.range originalBasis = Set.range basis := by
    ext x
    constructor
    · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
      exact Set.mem_range_self j
    · rintro ⟨j, rfl⟩
      exact ⟨originalBasis j, Set.mem_range_self j, rfl⟩
  rw [himage, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator

def selected : Fin @RANK@ → Fin @BASIS@ := @SELECTED@
def quotientWords : Fin @BASIS@ → List (Fin @RANK@) := @QWORDS@
private def residueRow : Fin @BASIS@ → Fin @ROWS@ := @RESIDUES@

private theorem relation_pointwise : ∀ (j : Fin @BASIS@) (x : Fin 16),
    BinaryCarrierDerivedRadical16T@MASTER@.ambientRows (residueRow j) x =
      (BinaryCarrierDerivedRadical16T@MASTER@.ambientBasis j *
        (((quotientWords j).map
          (BinaryCarrierDerivedRadical16T@MASTER@.ambientBasis ∘ selected)).prod)⁻¹) x := by
  decide +kernel

theorem quotientWords_mem_radical (j : Fin @BASIS@) :
    ((originalBasis j * (((quotientWords j).map (originalBasis ∘ selected)).prod)⁻¹ : D) : Original) ∈
      primeRelativeRadical 2 D := by
  have he :
      ((originalBasis j * (((quotientWords j).map (originalBasis ∘ selected)).prod)⁻¹ : D) : Original) =
        BinaryCarrierDerivedRadical16T@MASTER@.elements (residueRow j) := by
    apply Subtype.ext
    let projection : D →* Equiv.Perm (Fin 16) := Original.subtype.comp D.subtype
    change projection (originalBasis j * (((quotientWords j).map (originalBasis ∘ selected)).prod)⁻¹) =
      (BinaryCarrierDerivedRadical16T@MASTER@.elements (residueRow j) : Equiv.Perm (Fin 16))
    have hf : projection ∘ (originalBasis ∘ selected) =
        BinaryCarrierDerivedRadical16T@MASTER@.ambientBasis ∘ selected := by
      funext i
      exact BinaryCarrierDerivedRadical16T@MASTER@.basis_coe (selected i)
    have hb : projection (originalBasis j) = BinaryCarrierDerivedRadical16T@MASTER@.ambientBasis j :=
      BinaryCarrierDerivedRadical16T@MASTER@.basis_coe j
    rw [map_mul, map_inv, map_list_prod, List.map_map, hf, hb,
      BinaryCarrierDerivedRadical16T@MASTER@.elements_coe]
    exact (Equiv.ext (relation_pointwise j)).symm
  rw [he]
  exact BinaryCarrierDerivedRadical16T@MASTER@.elements_mem_radical _

def coordinates : Characters →ₗ[ZMod 2] (Fin @RANK@ → ZMod 2) :=
  primeRelativeCharacterCoordinates 2 D originalBasis selected

@[simp] theorem coordinates_apply (χ : Characters) (i : Fin @RANK@) :
    coordinates χ i = χ.1 (Additive.ofMul (originalBasis (selected i))) := rfl

theorem originalBasis_value (χ : Characters) (j : Fin @BASIS@) :
    χ.1 (Additive.ofMul (originalBasis j)) = ((quotientWords j).map (coordinates χ)).sum :=
  primeRelativeCharacter_generator_values 2 D originalBasis selected quotientWords
    quotientWords_mem_radical χ j

theorem coordinates_injective : Function.Injective coordinates :=
  primeRelativeCharacterCoordinates_injective 2 D originalBasis originalBasis_full selected quotientWords
    quotientWords_mem_radical

def coordinateEquiv : Characters ≃ₗ[ZMod 2] (Fin @RANK@ → ZMod 2) :=
  primeRelativeCharacterCoordinateEquiv 2 D originalBasis originalBasis_full selected quotientWords
    quotientWords_mem_radical BinaryCarrierDerivedRadical16T@MASTER@.relative_character_rank

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T@MASTER@
'''


def vector(xs):
    return '![' + ','.join(map(str, xs)) + ']'


def emit(master, data):
    substitutions = dict(MASTER=master, ROWS=len(data['rows']), RANK=len(data['selected']),
        BASIS=data['basis_count'], GENERATORS=data['original_count'], CANDIDATES=len(data['seeds']),
        SEEDS=vector([f'.inl {s[1]}' if s[0]=='pow' else f'.inr ({s[1]},{s[2]})' for s in data['seeds']]),
        WORDS=vector(['['+','.join(map(str,w))+']' for w in data['words']]),
        NEXT=vector([vector(r) for r in data['next']]),
        CONJUGATES=vector([vector(r) for r in data['conjugates']]), POWERS=vector(data['powers']),
        MIXED=vector([vector(r) for r in data['mixed']]), SELECTED=vector(data['selected']),
        QWORDS=vector(['['+','.join(map(str,w))+']' for w in data['qwords']]), RESIDUES=vector(data['residues']))
    result = {}
    for prefix, template in [('BinaryCarrierDerivedRadical', RADICAL), ('BinaryCarrierDerivedCharacters', CHARACTERS)]:
        for key, value in substitutions.items():
            template = template.replace(f'@{key}@', str(value))
        require(re.search(r'@[A-Z_]+@', template) is None, 'unexpanded template token')
        content = template.encode()
        require(len(content) <= MAX_OUTPUT_BYTES, 'output byte ceiling reached')
        result[OUT/f'{prefix}16T{master}.lean'] = content
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--master', type=int, required=True, choices=[1083,1084,1332,1547])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--max-radical-rows', type=int, default=8)
    parser.add_argument('--max-operations', type=int, default=MAX_OPERATIONS)
    parser.add_argument('--seconds', type=float, default=MAX_SECONDS)
    args = parser.parse_args()
    require(1 <= args.max_radical_rows <= 8, 'invalid radical-row budget')
    require(1 <= args.max_operations <= MAX_OPERATIONS, 'invalid operation budget')
    require(0 < args.seconds <= MAX_SECONDS, 'invalid time budget')
    require(not(args.check and args.report), '--check cannot write a report')
    report = args.report.resolve() if args.report else None
    if report:
        require(not report.is_relative_to(ROOT) and report.parent.is_dir() and report.suffix=='.json',
                'report must be an external .json in an existing directory')
    budget = square.Budget(64,args.max_operations,args.seconds,time.monotonic())
    g, snapshots = square.selected_generators(args.master)
    for p in [Path(__file__).resolve(),Path(derived.__file__).resolve(),Path(square.__file__).resolve()]:
        snapshots[p] = square.bounded_read(p)
    data = search(g,budget,args.max_radical_rows)
    dependency = OUT/f'BinaryCarrierDerivedOrder16T{args.master}.lean'
    snapshots[dependency] = square.bounded_read(dependency)
    require(snapshots[dependency] == derived.emit(args.master,data['D']), 'derived prerequisite bytes differ')
    outputs = emit(args.master,data)
    for p,content in outputs.items():
        require(OUT.resolve().is_relative_to(ROOT) and not p.is_symlink(), 'output escapes publication')
        if args.check:
            require(p.is_file() and square.bounded_read(p)==content, f'output bytes differ: {p.name}')
    for p,content in snapshots.items():
        require(square.bounded_read(p)==content, 'source changed during production')
    budget.time_check()
    summary = dict(master=args.master,radical_rows=len(data['rows']),character_dimension=len(data['selected']),
        selected=data['selected'],quotient_words=data['qwords'],operations=budget.operations,
        seconds=time.monotonic()-budget.start,checked_bytes=args.check,write_requested=args.write,
        outputs={str(p.relative_to(ROOT)):hashlib.sha256(content).hexdigest() for p,content in outputs.items()})
    # Prepare and validate every payload before the first output mutation.
    report_content = None
    if report:
        detail={**summary,'status':'untrusted selected witnesses; actual Lean checks required',
            'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(v).hexdigest() for p,v in snapshots.items()},
            **{k:v for k,v in data.items() if k!='D'}}
        report_content=(json.dumps(detail,indent=2)+'\n').encode()
        require(len(report_content)<=MAX_OUTPUT_BYTES,'report byte ceiling reached')
    budget.time_check()
    if args.write:
        for p,content in outputs.items():
            if not p.is_file() or square.bounded_read(p)!=content:
                square.atomic_write(p,content)
    if report_content is not None:
        square.atomic_write(report,report_content)
    print(json.dumps(summary,sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (square.CertificateError,OSError,UnicodeError,RecursionError,json.JSONDecodeError) as error:
        print(f'selected relative-derived coordinates: {error}',file=sys.stderr)
        raise SystemExit(2)
