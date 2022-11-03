-- albert zeng
-- tcf5pw@virginia.edu

/-
CS2120 Fall 2022 Sullivan. Quiz #1. Edit your answers into
this file using VSCode. Save the file to your *local* hard 
drive (File > Save As > local > ...). Submit it to the Quiz1
assignment on Collab.
-/

/-
#1: For each of the following questions give a yes/no answer 
and then a very brief explanation why that answer is correct.
To explain why your answer is correct, name the specific rule
of inference that tells you it's correct, or explain that 
there is no such valid inference rule.
-/

/-
#1A

If a ball, b, is round *and* b is also red, is b red?

A: yes/no: yes

B: Why? and elimination (right)


#1B

If flowers make you happy and chocolates make you happy,
and I give you flowers *or* I give you chocolates, will
you be happy?

A: yes/no: yes

B: Why? or elimination


#1C: If giraffes are just zebras in disguise, then the 
moon is made of green cheese?

A. yes/no: yes

B. Why? ex falso quodlibet -- if something false is
        considered true, anything that follows is true


#1D. If x = y implies that 0 = 1, then is it true that
x ≠ y?

A. yes/no: yes

B. Why? anything that implies a false statement must itself
        also be false (can't have true implies false)



#1E. If every zebra has stripes and Zoe is a Zebra then
Zoe has stripes.

A. yes/no: yes

B. Why? arrow elimination


#1F. If Z could be *any* Zebra and Z has stripes, then 
*every* Zebra has stripes.

A. Yes/no: yes

B: Why? for all elimination


#1G. If whenever the wind blows, the leaves move, and 
the leaves are moving, then the wind is blowing.

A. yes/no: no

B. Why? no such valid inference rule (implies is not bidirectional)


#1H: If Gina is nice *or* Gina is tall, and Gina is nice,
then Gina is not tall. (The "or" here is understood to be
the or of predicate logic.)

A. yes/no: no

B. Why? no such valid inference rule (logical or is not exclusive)
-/



/- 
#2

Consider the following formula/proposition in propositional
logic: X ∨ ¬Y.

#2A: Is it satisfiable? If so, give a model (a binding of 
the variables to values that makes the expressions true).

This is satisfiable, since at least one interpretation of
X and Y is true:

   X   |   Y   | X ∨ ¬Y
------------------------
 false | false | true
 false | true  | false
 true  | false | true
 true  | true  | true


#2B: Is it valid? Explain your answer. 

This is not valid, since it is not true for every
interpretation of X and Y (when X is false and Y is true,
X or not Y is false)
-/


/-
#3: 

Express the following propositions in predicate logic, by
filling in the blank after the #check command.

If P and Q are arbitrary (any) propositions, then if (P is 
true if and only if Q is true) then if P is true then Q is 
true.
-/

#check (∀ (P Q : Prop), P == Q → P → Q)



/-
#4 Translate the following expressions into English.
The #check commands are just Lean commands and can
be ignored here. 
-/


-- A
#check ∀ (n m : ℕ), n < m → m - n > 0

/-
Answer: If n and m are arbitrary (any) natural numbers,
        then if n is lesser than m, then m subtracted
        by n (i.e. m - n) is greater than 0.
-/

-- B

#check ∃ (n : ℕ), ∀ (m : ℕ), m >= n

/-
Answer: There exists a natural number n such that, for
        every natural number m, m is greater than or
        equal to n.
-/


-- C

variables (isEven: ℕ → Prop) (isOdd: ℕ → Prop)
#check ∀ (n : ℕ), isEven n ∨ isOdd n

/-
Answer: For every natural number n, n is even or
        n is odd. 
-/


-- D

#check ∀ (P : Prop), P ∨ ¬P

/-
Answer: For every proposition P, P or the inverse
        of P (not P) is true.
-/


-- E

#check ∀ (P : Prop), ¬(P ∧ ¬P)

/-
Answer: For every proposition P, P and the inverse
        of P (not P) together is false (i.e. not true).
-/


/-
#5 Extra Credit

Next we define contagion as a proof of a slightly long
proposition. Everything before the comma introduces new
terms, which are then used after the comma to state the
main content of the proposition. 

Using the names we've given to the variables to infer
real-world meanings, state what the logic means in plain
natural English. Please don't just give a verbatim reading
of the formal logic. 
-/

variable contagion : 
  ∀ (Animal : Type) 
  (hasVirus : Animal → Prop) 
  (a1 a2 : Animal) 
  (hasVirus : Animal → Prop)
  (closeContact : Animal → Animal → Prop), 
  hasVirus a1 → closeContact a1 a2 → hasVirus a2

/-
Answer: Let's say that we have two animals. If the first animal is
        infected with a virus, and then if the infected animal
        comes into close contact with a second animal, then
        the second animal now also is infected with the virus.
-/