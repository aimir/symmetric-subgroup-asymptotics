import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovData

/-! The selected70-letter list is precisely two fixed-word templates.
This is a finite equality of displayed field parameters, separate from
its interpretation in the original fixed group. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordTemplates
open CFSGReeFFourFieldEightCertificateField
open CFSGReeFFourFieldEightKrylovData

abbrev Letter := Bool × (Fin 4 × Element)

def rootLetters (neg : Bool) (i : Fin 4) (t : Element) : List Letter :=
  if t = 0 then [] else [(neg, (i, t))]

def weylLetters (i : Fin 4) : List Letter :=
  rootLetters false i 1 ++ rootLetters true i 1 ++ rootLetters false i 1

def middleLetters (b c : Element) : List Letter :=
  rootLetters false 1 b ++ rootLetters false 2 (b^4) ++
    weylLetters 1 ++ rootLetters false 2 (c^4+b^2*b^4) ++
    (weylLetters 1).reverse ++ weylLetters 2 ++ rootLetters false 1 c ++
    (weylLetters 2).reverse

def blockLetters (a b c : Element) : List Letter :=
  rootLetters false 0 a ++ rootLetters false 3 (a^4) ++ middleLetters b c ++
    weylLetters 0 ++ weylLetters 3 ++ weylLetters 1 ++ weylLetters 2 ++
    weylLetters 1 ++ weylLetters 2

def selectedLetters : List Letter :=
  rootWord.map (fun x => (x.1, (x.2.1, ofBits x.2.2)))

theorem weylLetters_reverse (i : Fin 4) : (weylLetters i).reverse = weylLetters i := by
  simp [weylLetters, rootLetters]

theorem selectedLetters_eq : selectedLetters =
    blockLetters (ofBits 1) (ofBits 4) (ofBits 3) ++
      blockLetters (ofBits 7) (ofBits 1) (ofBits 0) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordTemplates
