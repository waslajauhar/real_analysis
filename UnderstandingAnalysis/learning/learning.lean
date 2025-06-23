-- Learning Pracice
--=======================day 1==============================--

def zeroEqualsZero : 0 = 0 := rfl
#check zeroEqualsZero

theorem theorem1 : 2 = 1+1 := rfl
#check theorem1
#reduce theorem1
#check theorem1

theorem theorem1' : 2 = 1 + 1 := by eq_refl
#check theorem1'
#reduce theorem1'

theorem theorem2 : false = false := rfl

#check theorem2

theorem theorem3 : False = False := by rfl

theorem theorem4 : "Hello Lean!" = "Hello " ++ "Lean!" := rfl
#check theorem4
#reduce theorem4
#check theorem4

theorem theorem5 : 3*3 + 4*4 = 5*5 := by eq_refl
#check theorem5
#reduce theorem5

#check Eq.symm

theorem thm7 : "wasla" ++ "jauhar" = "waslajauhar" := rfl

#check Eq.symm

def a := 1
def b := 1

#check a
#eval a
#reduce a

theorem aEb : a = b := rfl
#check aEb
#check Eq.symm aEb
def es := Eq.symm aEb
def es2 := Eq.symm es
#check es
#check es2

def c := 1
theorem bEc : b = c := rfl

#check Eq.trans aEb bEc


-------------------------------------

def trans2 {a b c: Type} (ab: a=b) (cb: c = b) :=
  Eq.trans ab (Eq.symm cb)

#check trans2

theorem cEb : c = b := rfl
#check cEb

-- Build theorem, using trans2 -> a = c

theorem aEc : a = c := Eq.trans2 aEb cEb
#check aEc

-------------------------------------------------------

theorem zEz : 0 = 0 := Eq.refl 0

theorem zEqz : 0 = 0 := by
{
  have zEqz := Eq.refl 0;
  exact zEqz;
}

#check zeqz

theorem t : True := True.intro

theorem fl : False := False.intro -- can't do in the case of false. 

#check t

theorem t' : True := by
  apply True.intro

axiom f : False

theorem zeroEqualsOne : 0 = 1 := False.elim f

axiom d : x = y

#check False.elim

----------------------------------------------------------

#check And.intro

def P := 0 = 0
#check P
def Q : Prop := 1 = 1

theorem pfP : P := Eq.refl 0
theorem pfQ : Q := Eq.refl 1

def PandQ : Prop := P ∧ Q
#check PandQ
#check P ∧ Q

theorem pfPQ : P ∧ Q :=
  And.intro pfP pfQ

theorem pAq : P ∧ Q := by
{
  apply And.intro;
  exact Eq.refl 0
  exact Eq.refl 1
}

#check pAq

---------------------------------------------

variable (A B : Prop)
variable (hA : A) (hB : B)

def proof_and_term : A ∧ B := And.intro hA hB

def proof_and_term' : A ∧ B := ⟨hA, hB⟩

def proof_and_tactic : A ∧ B := by
  apply And.intro
  exact hA 
  exact hB

--===========================day 2=============================--

theorem proof_pq : P ∧ Q := by
  have A := Eq.refl 0;
  have B := Eq.refl 1;
  apply And.intro A B;

#check And.left pfPQ
#check And.right pfPQ

theorem pfP' : P := And.left pfPQ
theorem pfQ' : Q := And.right pfPQ

theorem pfp : P := by
  exact And.left pfPQ

def qAp : Prop := Q ∧ P
theorem pfQP : Q ∧ P :=
  And.intro (And.right pfPQ) (And.left pfPQ)

theorem pfQP' : Q ∧ P := by {
  split;
  exact (And.right pfPQ);
  exact (And.left pfPQ);
}


theorem pfQP'' : Q ∧ P := by
  apply And.intro pfQ pfP

#check And.comm
#check and_comm

def and_com {P Q: Prop} (pAq: P ∧ Q) :=
  And.intro (And.right pAq) (And.left pAq)

theorem qAp' : Q ∧ P := and_com pfPQ

theorem QaP : P ∧ Q := pfPQ

-------------------------------------------------------------

/-
def and_Associative_R {P Q R : Prop}
  (pfPQ_R: (P ∧ Q) ∧ R) : 
  (P ∧ (Q ∧ R)) := by {
    have pfR := And.elim.right pfPQ_R;
    have pfPQ := And.left pfPQ_R;
    have pfP := And.right pfPQ_R;
    have pfQR := And.intro pfQ pfR;
    exact And.intro pfP pfQR;
}
--Above proof is wrong.-/

-------------------------------------------------------------
def and_Associative_R {P Q R: Prop}
  (pfPQ_R: (P ∧ Q) ∧ R) :
  (P ∧ (Q ∧ R)) := by
{
  cases pfPQ_R with
  | intro pq r =>
    cases pq with
    | intro p q =>
      exact ⟨p, ⟨q, r⟩⟩
}

def and_Associative_L {P Q R : Prop} (pfP_QR: (P ∧ (Q ∧ R))) :
    ((P ∧ Q) ∧ R) := by {
  cases pfP_QR with
  | intro p qr =>
    cases qr with
    | intro q r =>
      exact ⟨⟨p, q⟩, r⟩
}

theorem and_assoc_equiv {P Q R : Prop} :
    ((P ∧ Q) ∧ R) <-> (P ∧ (Q ∧ R)) :=
  ⟨and_Associative_R, and_Associative_L⟩
------------------------------------------------------------

--======================== day 3=============================--

def arrow_elim {P Q : Prop} (pfPtopfQ : P → Q) (pfP: P) : Q :=
  pfPtopfQ pfP

#check arrow_elim

variable (P Q : Prop)
variable (implies : P → Q)
variable (pfP : P)

#check implies pfP

section fIt

variable (falseImpTrue : False → True)

theorem zeroEqualsOne' : (0 = 1) :=
  False.elim (falseImpTrue True.intro)

#check zeroEqualsOne

end

def trueImpTrue (pfTrue: True) : True := pfTrue

#check trueImpTrue

axiom f : False
def trueImpFalse (pfTrue : True) : False :=
  False.elim f

#check trueImpFalse

def falseImpTrue (f: false) : True := True.intro
#check falseImpTrue

 
theorem fImpT_th : false → True := falseImpTrue

def fimpZeZ (f: false) : (0 = 1) := False.elim f

theorem falseIsZeroEqualsOne : false → 0 = 1 := fimpZeZ

#check falseIsZeroEqualsOne

-------------------------------------------------------------

def zeroNat (n : Nat) : Nat := 0
#check zeroNat 0
#reduce zeroNat 7

def indentityNat (n : Nat) : Nat := n
#reduce indentityNat 0909
#check indentityNat

def zeroNat' (n : Nat) : Nat := (0 : Nat)
#reduce zeroNat' 2

def zeroNat'' : Nat → Nat := (λ 0)
def zeroNat''' := λ n : Nat 0

def indentityNat' : Nat → Nat := λ n n

def zeroN : ℕ → ℕ := λ _ => 0

def zeroN' : ℕ → ℕ := fun _ => 0
#check zeroN'
#reduce zeroN' 0

def double: Nat → Nat := λ n : nat 2*n
#check double

def square (n: Nat) := n*n
#reduce square 3

def cube (n: Nat) := n * square n
#reduce cube 12

def square' : ℤ → ℤ := λ n, (n*n)

#reduce square' 12

def square' : ℤ → ℤ

def uint32 : Nat → Bool := λ n => if n >= 0 ∧ 2^3 then True else False

#check uint32
#reduce uint32 32
#reduce unint32 2

def uint32' (n : Nat) : Bool := if n <= 2^3 ∧ n >= 0 then true else false
#check uint32'

#reduce uint32' 1
#reduce uint32' 3
#reduce uint32' 12
#reduce uint32' 123

#reduce uint32' 8
#reduce uint32' 32
#reduce uint32' 7

def positive : Nat → Bool := λ n, if n > 0 then true else false : Bool

#reduce positive 2

theorem posIspos : isPositive = positive := rlf

def power (x: Nat) (y : Nat) := x^y
#eval power 2 32
#reduce power 5 12

def compose (f: Nat → Nat) (g: Nat → Nat) (x: Nat) : Nat :=
  f (g x)

#check compose
#check compose square double 3
#eval compose square double 3

#eval compose square double 3

def doTwice (f: Nat → Nat) : Nat := f (f x)a
#check doTwice

def doTwice' : (Nat → Nat) → Nat → Nat :=
  fun (f: Nat → Nat) (x : Nat), f (f x)


def doTwice'' : (Nat → Nat) → Nat → Nat :=
  fun (f: Nat → Nat) λ (x: Nat) f (f x)

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print doTwice

def twiceDub := (doTwice' double)

#eval twiceDub 3

def doTeqDoT : doTwice'' := rfl

def doTwicee (f: (Nat → Nat) → Nat → Nat) (x: (Nat → Nat)) : (Nat → Nat) :=
  f (f x)

#check doTwicee

#eval doTwicee 3

#reduce doTwicee

---------------------------------------------------

variable P : Prop

theorem same: (¬ P) = (P → False) := rfl

theorem zneqo : 0 != 1 := rfl
theorem ttneqff : true != false := rfl

#reduce Nat.zero
#reduce Nat.succ (Nat.succ (Nat.succ 0))

theorem zenqo' : 0 = 1 → False :=
  λ (h: Nat) : (0 = 1), Nat.no_confusion h


--========================day 4===========================--


