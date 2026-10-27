import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu22.Certificates.Words
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Certificates.Words
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.Certificates.Words
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-! Extension of the actual degree-22 permutation generators by fixed new
points. These are ambient permutation homomorphisms, not an identification
of any pinned presentation model. Only the two original generators are
checked at each target degree; every certificate word then follows by
homomorphism naturality. No new seed point tables or capacity occur. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTailPermutationExtension

def extend23 : Equiv.Perm (Fin 22) →* Equiv.Perm (Fin 23) :=
  Equiv.Perm.extendDomainHom (Fin.castLEquiv (by decide : 22 ≤ 23))

theorem extend23_a : extend23 CFSG.Certificates.Mathieu22.m22a = CFSG.Certificates.Mathieu23.m23a := by
  apply Equiv.ext
  intro p
  revert p
  decide +kernel

theorem extend23_b : extend23 CFSG.Certificates.Mathieu22.m22b = CFSG.Certificates.Mathieu23.m23b := by
  apply Equiv.ext
  intro p
  revert p
  decide +kernel

def letter23 : CFSG.Certificates.Mathieu22.M22Certificates.Gen → CFSG.Certificates.Mathieu23.M23Certificates.Gen
  | .a => .a
  | .aInv => .aInv
  | .b => .b
  | .bInv => .bInv

theorem letter23_toPerm (g : CFSG.Certificates.Mathieu22.M22Certificates.Gen) :
    extend23 g.toPerm = (letter23 g).toPerm := by
  cases g <;> simp only [CFSG.Certificates.Mathieu22.M22Certificates.Gen.toPerm,
    CFSG.Certificates.Mathieu23.M23Certificates.Gen.toPerm,letter23,map_inv,extend23_a,extend23_b]

theorem word23_eval (w : CFSG.Certificates.Mathieu22.M22Certificates.Word) :
    extend23 (CFSG.Certificates.Mathieu22.M22Certificates.Word.eval w) =
      CFSG.Certificates.Mathieu23.M23Certificates.Word.eval (w.map letter23) := by
  induction w with
  | nil => exact map_one _
  | cons g w ih =>
    simp only [CFSG.Certificates.Mathieu22.M22Certificates.Word.eval,List.map_cons,
      CFSG.Certificates.Mathieu23.M23Certificates.Word.eval,map_mul,ih,letter23_toPerm]

def extend24 : Equiv.Perm (Fin 22) →* Equiv.Perm (Fin 24) :=
  Equiv.Perm.extendDomainHom (Fin.castLEquiv (by decide : 22 ≤ 24))

theorem extend24_a : extend24 CFSG.Certificates.Mathieu22.m22a = CFSG.Certificates.Mathieu24.m24a := by
  apply Equiv.ext
  intro p
  revert p
  decide +kernel

theorem extend24_b : extend24 CFSG.Certificates.Mathieu22.m22b = CFSG.Certificates.Mathieu24.m24b := by
  apply Equiv.ext
  intro p
  revert p
  decide +kernel

def letter24 : CFSG.Certificates.Mathieu22.M22Certificates.Gen → CFSG.Certificates.Mathieu24.M24Certificates.Gen
  | .a => .a
  | .aInv => .aInv
  | .b => .b
  | .bInv => .bInv

theorem letter24_toPerm (g : CFSG.Certificates.Mathieu22.M22Certificates.Gen) :
    extend24 g.toPerm = (letter24 g).toPerm := by
  cases g <;> simp only [CFSG.Certificates.Mathieu22.M22Certificates.Gen.toPerm,
    CFSG.Certificates.Mathieu24.M24Certificates.Gen.toPerm,letter24,map_inv,extend24_a,extend24_b]

theorem word24_eval (w : CFSG.Certificates.Mathieu22.M22Certificates.Word) :
    extend24 (CFSG.Certificates.Mathieu22.M22Certificates.Word.eval w) =
      CFSG.Certificates.Mathieu24.M24Certificates.Word.eval (w.map letter24) := by
  induction w with
  | nil => exact map_one _
  | cons g w ih =>
    simp only [CFSG.Certificates.Mathieu22.M22Certificates.Word.eval,List.map_cons,
      CFSG.Certificates.Mathieu24.M24Certificates.Word.eval,map_mul,ih,letter24_toPerm]

end SymmetricSubgroupAsymptotics.CFSGMathieuTailPermutationExtension
