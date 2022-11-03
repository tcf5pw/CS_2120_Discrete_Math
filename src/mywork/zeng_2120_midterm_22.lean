-- albert zeng
-- tcf5pw@virginia.edu

/-
This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?
Answer: It is true.


-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
    split,
        apply false.elim,
        
        assume t,
        apply true.intro,
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer: By using the and elimination rules, it will
suffice to prove the left side of the and by itself
and the right side of the and by itself (left and
right and-elimination, respectively) to prove the
entire statement as a whole, since we can also use
the and-introduction rule with proofs of the left and
right sides of the statement to construct a proof of
the entire statement as a whole. On the left half,
using false elimination -- if false is true, anything
and everything else is also true -- suffices to show
that false implies true is true; on the right half,
using true introduction -- anything that implies true
results in an overall true statement, regardless of the
truthfulness of the preceding statement -- suffices to
show that true implies true is true.

-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as  (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rules makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: If the negation of P or Q is true, that means
that at least one of the two must be true (that is,
the negation of P, not P itself). If we also assume
that P is true, then Q must also be true since the
negation of P (which is true) is false and the disjunction
of the negation of P and Q must still be true.

-/



/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
f   t   t           f               t
t   f   f           f               t
t   t   t           t               t


Statement: Because every possible combination of truth
value inputs for P and Q results overall in an output
of true, then the statement must be valid.

-/  


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
    assume P Q h,
    cases and.elim_left h with np q,
        let f := np (and.elim_right h),
        apply false.elim f,

        exact q,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer: Using case analysis on the left half of the
and statement, which itself is an or statement, it will
suffice to prove the left half of the or statement and
the right half of the or statement individually. Assuming
that we have a proof of the negation of P, we can use and
elimination (on the right half) to obtain a proof of P.
Since we have both a proof of not P and P, we can use false
elimination on the two to obtain a proof of Q since anything
that follows a proof of false is true. For the second case,
we assume that Q is true, but Q is what we're looking for,
so we don't need to do anything more.

-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true.  Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
    ∀ (P Q : Prop),
    (P ↔ Q) → P → Q

/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/


/- Option #1: Informal proof:

-/


/-
Option #2: Formal proof. Reminders: the iff elim
rules are called iff.mp and iff.mpr in Lean; or you
can use "cases" to apply the two elimination rules 
to a proof of a bi-implication automatically.
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
    unfold if_p_iff_q_then_if_also_p_then_q,
    assume P Q h p,
    let left := iff.elim_left h,
    exact left p,
end




-- ****************** #4 [20 points] *******************

/- #



A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer: To prove the negation of P (not P) by negation,
we need to prove that P implies false -- if we assume a
proof of P, then we can derive a proof of false from that
proof of P. Since it is impossible to derive a proof of
false from a valid statement, it must be the case that P
cannot be true (i.e. the negation of P is true), since we
would be able to derive a proof of false under the premise
that P is true.

-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: To prove P by contradiction, we first assume that
the negation of P is true. If, by assuming a proof of the
negation of P, we are able to obtain a proof of false -- a
contradiction -- we can use negation introduction on the
negation of P to confirm that the negation of the negation
of P (not not P) is true. Finally, using negation elimination,
we can obtain a proof of P from a proof of not not P.

-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 


A. Is it hot in classical logic? 

Answer: Yes


B. Is it hot "constructively?" Briefly explain your answer. 
    
Answer: Yes -- using or elimination on "sunny or not sunny",
both of which imply that it's hot, it will always be hot
under the classical logic assumption of the excluded middle
(it will always be either sunny or not sunny -- there is no
in-between).


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
    assume S H s_true s_false,
    cases (classical.em S) with s ns,
        exact s_true s,

        exact s_false ns,
end

