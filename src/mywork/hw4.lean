-- albert zeng
-- tcf5pw@virginia.edu

/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that
logical and (∧) is associative. That is,
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is,
too. Replace the placeholder (_) with your
answer.
-/

def and_associative : Prop := 
  ∀ (P Q R : Prop),
  P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R


/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: If we have three propositions, P, Q, and R,
        and we also assume that the left proposition
        (the conjunction of P and the conjunction of
        Q and R) is true, we can use the left and right
        and-elimination rules to derive the truth of P,
        Q, and R separately. Then, using the and-
        introduction rule, we can construct the right
        proposition (the conjunction of, the conjunction
        of P and Q, and R). Similarly, we can reverse
        the process (starting with the right proposition
        and constructing the left proposition) to confirm
        the bidirecitonality (iff) of and_associative.
-/

/- #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem and_assoc_true : and_associative :=
begin
  unfold and_associative,
  assume P Q R,
  split,
    assume h,
    let h1 := and.elim_right h,
    let p : P := and.elim_left h,
    let q : Q := and.elim_left h1,
    let r : R := and.elim_right h1,
    let c := and.intro p q,
    apply and.intro c r,

    assume h,
    let h1 := and.elim_left h,
    let p : P := and.elim_left h1,
    let q : Q := and.elim_right h1,
    let r : R := and.elim_right h,
    let c := and.intro q r,
    apply and.intro p c,
end


/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (P Q R : Prop),
  P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.

Answer: If we have three propositions, P, Q, and R,
        and we also assume that the left proposition
        (the disjunction of P and the disjunction of
        Q and R) is true, we can split the problem
        into several cases where we assume each side
        of each or connector is true. Starting with
        the left proposition, we have two cases: if
        P is true and if the disjunction of Q and R
        is true. We can furthermore obtain three cases
        by splitting the Q and R case into if Q is
        true and if R is true, separately. Then, using
        various left and right or-introduction rules,
        we can construct the right proposition (the
        disjunction of, the disjunction of P and Q,
        and R). Similarly, we can reverse the process
        (starting with the right proposition and
        constructing the left proposition) to confirm
        the bidirecitonality (iff) of or_associative.
-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
  unfold or_associative,
  assume P Q R,
  split,
    assume h,
    cases h with p qr,
      let c := or.intro_left Q p, -- same as "or.inl p"
      apply or.intro_left R c,
    
      cases qr with q r,
        let c := or.intro_right P q, -- same as "or.inr q"
        apply or.intro_left R c,

        apply or.intro_right (P ∨ Q) r,

    assume h,
    cases h with pq r,
      cases pq with p q,
        apply or.intro_left (Q ∨ R) p,
        
        let c := or.intro_left R q,
        apply or.intro_right P c,
      
      let c := or.intro_right Q r,
      apply or.intro_right P c,
end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  ∀ (X Y Z : Prop),
  (X → Y) → (Y → Z) → (X → Z)


/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and X, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.

Answer: If we have three propositions, X, Y, and Z,
        and we assume that we have a proof of X
        implies Y, and then we also have a proof of
        Y implies Z, and we start by assuming that
        we have a proof of X, we can use the proof of
        X implies Y to obtain a proof of Y. Similarly,
        we can use the proof of Y implies Z to obtain
        a proof of Z, which would make X implies Z
        true, since we obtained the proof of Y under
        the assumption that X is true.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/

theorem arrow_transitive_true : arrow_transitive :=
begin
unfold arrow_transitive,
assume X Y Z,
assume xy yz x,
let y := xy x,
let z := yz y,
exact z,
end


/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Wet → ¬Raining)


/- #4B [10 points].
-/

theorem contrapositive_valid : contrapositive :=
begin
unfold contrapositive,
assume R W rw notw r,
let w := rw r,
let notr := notw w,
apply false.elim notr,
end

/- #4C [5 points]. 

Give an English language proof of it.

Answer: If we have two propositions, Raining and
        Wet, and we assume that if we have a proof
        of Raining implies Wet and we have a proof
        of Raining, then we can obtain a proof of
        Wet. Then, if we also have a proof of not
        Wet (i.e. Wet implies false), we can use
        false elimination to verify not Raining.
-/


/- #5. Extra credit.

Complete the following formal proof of the
proposition that if for any proposition P,
P ∨ ¬P is true, then for any propositions,
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y
is true. 
-/

theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nxory,
cases (em X) with x nx,
  let c := or.intro_left Y x,
  apply false.elim (nxory c),

  cases (em Y) with y ny,
    let c := or.intro_right X y,
    apply false.elim (nxory c),

    apply and.intro nx ny,
end


/-
A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: a
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as a proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: a proof of the left or of 
the right side, respectively.
-/
end