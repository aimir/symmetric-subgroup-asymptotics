#!/usr/bin/env python3
"""One bounded GL(3,2) pilot; no GAP, input databases, or bulk mode.

Run only by the primary agent. This emits a 168-row sparse matrix Cayley
certificate and ordinary bidirectional words for subgroup adjunctions.
The finite search is untrusted: generated Lean proofs check every equation.
All writes require an explicit output directory. Receipt is stdout only.
"""

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import time


class Pilot:
    def __init__(self):
        self.started = time.monotonic()
        self.operations = 0
        self.limit = 12_000_000

    def tick(self, n=1):
        self.operations += n
        if self.operations > self.limit:
            raise RuntimeError("selected pilot exceeded 12 million operations")
        if self.operations % 4096 < n and time.monotonic() - self.started > 45:
            raise RuntimeError("selected pilot exceeded 45 seconds")

    def matrix_mul(self, a, b):
        self.tick()
        result = 0
        for i in range(3):
            for j in range(3):
                bit = 0
                for k in range(3):
                    bit ^= ((a >> (3*i+k)) & 1) & ((b >> (3*k+j)) & 1)
                result |= bit << (3*i+j)
        return result

    def discover(self):
        identity, generators = 273, (275, 98)
        parents, letters, ranks = {identity: identity}, {identity: 0}, {identity: 0}
        todo = deque([identity])
        while todo:
            a = todo.popleft()
            for j, b in enumerate(generators):
                c = self.matrix_mul(a, b)
                if c not in parents:
                    if len(parents) >= 168:
                        raise RuntimeError("ambient exceeds selected 168-row cap")
                    parents[c], letters[c], ranks[c] = a, j, len(parents)
                    todo.append(c)
        if len(parents) != 168:
            raise RuntimeError("selected matrices did not generate 168 elements")
        self.codes = sorted(parents)
        self.index = {a: i for i, a in enumerate(self.codes)}
        self.one = self.index[identity]
        self.gens = tuple(self.index[g] for g in generators)
        self.parent = [self.index[parents[a]] for a in self.codes]
        self.letter = [letters[a] for a in self.codes]
        self.rank = [ranks[a] for a in self.codes]
        self.mul = [[self.index[self.matrix_mul(a, b)] for b in self.codes]
                    for a in self.codes]
        self.inv = [next(j for j in range(168) if self.mul[i][j] == self.one)
                    for i in range(168)]
        self.conj = [[self.mul[self.mul[c][a]][self.inv[c]] for a in range(168)]
                     for c in range(168)]
        self.next = [[self.mul[i][g] for g in self.gens] for i in range(168)]
        self.prev = [[self.mul[i][self.inv[g]] for g in self.gens] for i in range(168)]
        self.reps, self.rep_gens, self.lookup = [], [], {}
        self.register(frozenset([self.one]), [])
        transitions = []
        row = 0
        while row < len(self.reps):
            if len(self.reps) > 20:
                raise RuntimeError("selected subgroup class cap20 exceeded")
            old = self.rep_gens[row]
            row_transitions = []
            for g in range(168):
                source_gens = [g] + old
                words = self.word_bfs(source_gens)
                subgroup = frozenset(words)
                if subgroup not in self.lookup:
                    self.register(subgroup, source_gens)
                j, c = self.lookup[subgroup]
                target_words = self.word_bfs(self.rep_gens[j])
                forward = [target_words[self.conj[c][a]] for a in source_gens]
                backward = [words[self.conj[self.inv[c]][b]] for b in self.rep_gens[j]]
                row_transitions.append((j, c, forward, backward))
            transitions.append(row_transitions)
            row += 1
        if len(self.reps) != 15:
            raise RuntimeError(f"expected 15 conjugacy classes, found {len(self.reps)}")
        if len(self.lookup) > 256:
            raise RuntimeError("selected raw subgroup cap256 exceeded")
        self.transitions = transitions

    def word_bfs(self, generators):
        words = {self.one: []}
        todo = deque([self.one])
        signed = [(g, j, False) for j, g in enumerate(generators)]
        signed += [(self.inv[g], j, True) for j, g in enumerate(generators)]
        while todo:
            a = todo.popleft()
            for g, j, inverse in signed:
                self.tick()
                b = self.mul[a][g]
                if b not in words:
                    words[b] = words[a] + [(j, inverse)]
                    todo.append(b)
        return words

    def register(self, subgroup, generators):
        conjugates = []
        for c in range(168):
            self.tick(len(subgroup))
            conjugates.append(frozenset(self.conj[c][a] for a in subgroup))
        canonical = min(conjugates, key=lambda s: tuple(sorted(s)))
        c = conjugates.index(canonical)
        candidates = [self.conj[c][g] for g in generators if g != self.one]
        chosen, generated = [], frozenset([self.one])
        for g in candidates:
            if g not in generated:
                chosen.append(g)
                generated = frozenset(self.word_bfs(chosen))
        if generated != canonical or len(chosen) > 3:
            raise RuntimeError("selected representative requires more than three generators")
        chosen += [self.one] * (3-len(chosen))
        j = len(self.reps)
        self.reps.append(canonical)
        self.rep_gens.append(chosen)
        for d in range(168):
            self.tick(len(canonical))
            t = frozenset(self.conj[d][a] for a in canonical)
            # conj(d) canonical=t, hence conj(d^-1)t=canonical.
            self.lookup.setdefault(t, (j, self.inv[d]))


def balanced(expressions, variable="i.val", lo=0):
    if len(expressions) == 1:
        return expressions[0]
    m = len(expressions)//2
    return (f"(if {variable} < {lo+m} then {balanced(expressions[:m], variable, lo)} "
            f"else {balanced(expressions[m:], variable, lo+m)})")


def vec(xs):
    return "![" + ", ".join(map(str, xs)) + "]"


def row_function(name, rows, result_type, index_count=168):
    return (f"def {name} (i : Fin {index_count}) : {result_type} :=\n  "
            + balanced([str(x) for x in rows]) + "\n")


def two_function(name, rows, column_count, result_type):
    return (f"def {name} (i : Fin 168) (j : Fin {column_count}) : {result_type} :=\n  ("
            + balanced([vec(r) for r in rows])
            + ") j\n")


def split_check(n, maximum=8):
    if n <= maximum:
        return "(by decide +kernel)"
    left = n//2
    return (f"(Fin.addCases (m := {left}) (n := {n-left}) "
            f"{split_check(left, maximum)} {split_check(n-left, maximum)})")


def lean_word(word):
    terms = [f"(.inv (.generator {j}))" if inverse else f"(.generator {j})"
             for j, inverse in word]
    if not terms:
        return ".one"
    def build(xs):
        if len(xs) == 1:
            return xs[0]
        k = len(xs)//2
        return f"(.mul {build(xs[:k])} {build(xs[k:])})"
    return build(terms)


def cayley_source(p):
    s = """import SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixEncoding
import Mathlib.Order.Fin.Basic

/-! Selected GL(3,2) pilot. Sparse right-generator edges and predecessor
words certify the actual matrix group; no multiplication table is emitted. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoCayley
open GeneralThreeTwoMatrixEncoding
"""
    s += row_function("codes", p.codes, "Fin 512")
    s += row_function("ranks", p.rank, "ℕ")
    s += row_function("parents", p.parent, "Fin 168")
    s += row_function("letters", p.letter, "Fin 2")
    s += two_function("nextRow", p.next, 2, "Fin 168")
    s += two_function("prevRow", p.prev, 2, "Fin 168")
    s += f"""
def certificate : EncodedCayleyCertificate encoding 168 where
  rows := codes
  identity := {p.one}
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := {split_check(168)}
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := {split_check(168)}
  parent_next := {split_check(168)}

theorem rows_injective : Function.Injective certificate.rows :=
  (Fin.strictMono_iff_lt_succ.mpr {split_check(167)} : StrictMono codes).injective

theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  {split_check(168)}

abbrev Source := FiniteGroupRow 168
@[reducible] def group : Group Source :=
  certificate.rowGroup rows_injective prevRow prev_checked
local instance : Group Source := group

theorem generated_eq_top : Subgroup.closure (Set.range generators) = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [certificate.card_closure rows_injective,
    StandardThreeDimensionalLinearGroups.card_GL_two]

/-- This is the actual GL(3,2), not an abstract group with the same order. -/
def matrixEquiv : Source ≃* Ambient :=
  MulEquiv.ofBijective (certificate.rowHom rows_injective prevRow prev_checked)
    ⟨certificate.rowHom_injective rows_injective prevRow prev_checked, by
      apply MonoidHom.range_eq_top.mp
      rw [certificate.rowHom_range rows_injective prevRow prev_checked, generated_eq_top]⟩

end SymmetricSubgroupAsymptotics.GeneralThreeTwoCayley
end
"""
    return s


def rows_source(p):
    s = """import SymmetricSubgroupAsymptotics.GeneralThreeTwoCayley
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionWords

/-! Fifteen literal subgroups in the selected actual GL(3,2) row model.
Local adjunction equations, proved separately, establish their coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupRows
open GeneralThreeTwoCayley
local instance : Group Source := group
"""
    s += "def generators (i : Fin 15) (j : Fin 3) : Source :=\n  ("
    s += balanced([vec([f"⟨{g}⟩" for g in gs]) for gs in p.rep_gens]) + ") j\n"
    s += """
def rows (i : Fin 15) : Subgroup Source :=
  Subgroup.closure (Set.range (generators i))

theorem row_zero : rows 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  change generators 0 j = 1
  fin_cases j <;> decide +kernel

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupRows
end
"""
    return s


def matrix_rows_source(p):
    s = """import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupRows

/-! Explicit matrix values and inverse indices for the selected168 rows.
This validates ordinary words directly in the actual matrix group, avoiding
repeated predecessor walks in the executable abstract row operations. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixRows
open GeneralThreeTwoCayley GeneralThreeTwoMatrixEncoding
local instance : Group Source := group
"""
    s += row_function("inverseIndex", p.inv, "Fin 168")
    s += f"""
private theorem inverse_right : ∀ i : Fin 168,
    decode (codes i) * decode (codes (inverseIndex i)) = 1 :=
  {split_check(168, 2)}

private theorem inverse_left : ∀ i : Fin 168,
    decode (codes (inverseIndex i)) * decode (codes i) = 1 :=
  {split_check(168, 2)}

def matrixRows (i : Fin 168) : Ambient where
  val := decode (codes i)
  inv := decode (codes (inverseIndex i))
  val_inv := inverse_right i
  inv_val := inverse_left i

theorem matrixEquiv_row (i : Fin 168) : matrixEquiv ⟨i⟩ = matrixRows i := by
  apply Units.ext
  have h : encode ((matrixEquiv ⟨i⟩).val) = codes i :=
    certificate.encode_elements i
  simpa only [decode_encode] using congrArg decode h

theorem matrixEquiv_apply (g : Source) : matrixEquiv g = matrixRows g.index := by
  obtain ⟨i⟩ := g
  exact matrixEquiv_row i

end SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixRows
end
"""
    return s


def transition_source(p, row):
    transitions = p.transitions[row]
    namespace = f"GeneralThreeTwoSubgroupStep{row}"
    s = f"""import SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixRows

/-! Selected adjunctions from literal subgroup row {row}. Ordinary words
check both inclusions after the displayed actual ambient conjugation. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.{namespace}
open GeneralThreeTwoCayley GeneralThreeTwoSubgroupRows GeneralThreeTwoMatrixRows
local instance : Group Source := group
"""
    s += row_function("target", [t[0] for t in transitions], "Fin 15")
    s += row_function("conjugator", [f"⟨{t[1]}⟩" for t in transitions], "Source")
    forward = [[lean_word(w) for w in t[2]] for t in transitions]
    backward = [[lean_word(w) for w in t[3]] for t in transitions]
    s += two_function("forwardWord", forward, 4, "FiniteGeneratorWord (Fin 3)")
    s += two_function("backwardWord", backward, 3, "FiniteGeneratorWord (Fin 4)")
    s += f"""
private theorem forward_matrix_checked : ∀ i j,
    (forwardWord i j).eval (fun k => matrixRows (generators (target i) k).index) =
      MulAut.conj (matrixRows (conjugator i).index)
        (matrixRows ((Matrix.vecCons (⟨i⟩ : Source) (generators {row})) j).index) :=
  {split_check(168, 2)}

private theorem backward_matrix_checked : ∀ i j,
    (backwardWord i j).eval
        (fun k => matrixRows ((Matrix.vecCons (⟨i⟩ : Source) (generators {row})) k).index) =
      (MulAut.conj (matrixRows (conjugator i).index)).symm
        (matrixRows (generators (target i) j).index) :=
  {split_check(168, 2)}

private theorem forward_checked (i : Fin 168) (j : Fin 4) :
    (forwardWord i j).eval (generators (target i)) =
      MulAut.conj (conjugator i) ((Matrix.vecCons (⟨i⟩ : Source) (generators {row})) j) := by
  apply matrixEquiv.injective
  change matrixEquiv.toMonoidHom ((forwardWord i j).eval (generators (target i))) =
    matrixEquiv.toMonoidHom
      (MulAut.conj (conjugator i) ((Matrix.vecCons (⟨i⟩ : Source) (generators {row})) j))
  rw [FiniteGeneratorWord.map_eval, MulAut.conj_apply, map_mul, map_mul, map_inv]
  simpa only [MulEquiv.coe_toMonoidHom, matrixEquiv_apply,
    MulAut.conj_apply, map_mul, map_inv] using forward_matrix_checked i j

private theorem backward_checked (i : Fin 168) (j : Fin 3) :
    (backwardWord i j).eval (Matrix.vecCons (⟨i⟩ : Source) (generators {row})) =
      (MulAut.conj (conjugator i)).symm (generators (target i) j) := by
  apply matrixEquiv.injective
  change matrixEquiv.toMonoidHom
      ((backwardWord i j).eval (Matrix.vecCons (⟨i⟩ : Source) (generators {row}))) =
    matrixEquiv.toMonoidHom ((MulAut.conj (conjugator i)).symm (generators (target i) j))
  rw [FiniteGeneratorWord.map_eval, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
  simpa only [MulEquiv.coe_toMonoidHom, matrixEquiv_apply,
    MulAut.conj_symm_apply, map_mul, map_inv] using backward_matrix_checked i j

def certificate (i : Fin 168) :
    FiniteGeneratorEquivWordCertificate (MulAut.conj (conjugator i))
      (Matrix.vecCons (⟨i⟩ : Source) (generators {row})) (generators (target i)) where
  forward := {{ words := forwardWord i, equations := forward_checked i }}
  backward := {{ words := backwardWord i, equations := backward_checked i }}

theorem step (g : Source) : ∃ j : Fin 15, ∃ c : Source,
    MulAut.conj c • (rows {row} ⊔ Subgroup.closure {{g}}) = rows j := by
  obtain ⟨i⟩ := g
  exact ⟨target i, conjugator i,
    FiniteSubgroupAdjunctionCoverage.adjoin_eq_of_words _ _ _ _ (certificate i)⟩

end SymmetricSubgroupAsymptotics.{namespace}
end
"""
    return s


def complete_source():
    s = "".join(f"import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep{i}\n"
                for i in range(15))
    s += """
/-! Actual exhaustive subgroup conjugacy coverage from the checked local
adjunction equations. No subgroup-classification premise is imported. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupCoverage
open GeneralThreeTwoCayley GeneralThreeTwoSubgroupRows
local instance : Group Source := group

theorem step (i : Fin 15) (g : Source) : ∃ j : Fin 15, ∃ c : Source,
    MulAut.conj c • (rows i ⊔ Subgroup.closure {g}) = rows j := by
  fin_cases i
"""
    s += "".join(f"  · exact GeneralThreeTwoSubgroupStep{i}.step g\n" for i in range(15))
    s += """
theorem complete (U : Subgroup Source) :
    ∃ i : Fin 15, ∃ c : Source, MulAut.conj c • U = rows i :=
  FiniteSubgroupAdjunctionCoverage.complete rows ⟨0, row_zero⟩ step U

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupCoverage
end
"""
    return s


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    pilot = Pilot()
    pilot.discover()
    sources = {"GeneralThreeTwoCayley.lean": cayley_source(pilot),
               "GeneralThreeTwoSubgroupRows.lean": rows_source(pilot),
               "GeneralThreeTwoMatrixRows.lean": matrix_rows_source(pilot),
               "GeneralThreeTwoSubgroupCoverage.lean": complete_source()}
    sources.update({f"GeneralThreeTwoSubgroupStep{i}.lean": transition_source(pilot, i)
                    for i in range(15)})
    total_bytes = sum(len(s.encode()) for s in sources.values())
    if total_bytes > 8_000_000:
        raise RuntimeError("selected source cap8MB exceeded; split/simplify before retry")
    output.mkdir(parents=True, exist_ok=True)
    for name, source in sources.items():
        path = output/name
        if path.exists() and path.read_text() != source:
            raise RuntimeError(f"refusing to overwrite different source {path}")
        path.write_text(source)
    receipt = {"source": "literal binary 3x3 matrices, transvection and coordinate cycle",
               "ambient_order": 168, "subgroup_classes": len(pilot.reps),
               "raw_subgroups": len(pilot.lookup), "adjunctions": 168*len(pilot.reps),
               "row_orders": [len(r) for r in pilot.reps],
               "row_generators": pilot.rep_gens, "codes": pilot.codes,
               "operations": pilot.operations, "wall_seconds": time.monotonic()-pilot.started,
               "lean_bytes": total_bytes,
               "files": {name: hashlib.sha256(s.encode()).hexdigest()
                         for name, s in sources.items()}}
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
