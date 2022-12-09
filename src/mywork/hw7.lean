-- albert zeng
-- tcf5pw@virginia.edu

import data.set

/- #1

Formally prove that if there's an object, a, of some
type, α, having some property (satisfying a predicate),
P, then not every object of type α fails to have property,
P. Add a brief comment before each line of your proof
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
-- declaring what we can work with
assume exist all,
-- if we have exists then we have witness and proof of witness
cases exist with w Pw,
-- apply the for-all assumption to the witness above
let contra := all w,
-- contradiction: witness can't satisfy and not satisfy predicate
contradiction,
end


/- Extra credit.

The converse of this proposition is clasically true. If
not every object lacks property, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.

Proving the converse in constructive logic results in a sort
of roadblock since there is no information to be obtained
constructively from the "if not every object doesn't have
property P", so we can't get a witness and a proof of it
required for the final goal.
-/

example (α : Type) (P : α → Prop) : (¬(∀ x, ¬ P x)) → (∃ a, P a) :=
begin
assume notall,
-- since it's constructive logic we can't use classical excluded middle
-- which would be necessary to bypass the nots in the for all to obtain
-- a witness and its proof for the exists statement
end


/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive?
No - not the entire domain is included in the relation
(only 1, 2, and 3 were included, not any of the other
natural numbers)
B. Is this relation symmetric?
Yes - since the outputs of the three inputs are exactly
the same as their respective inputs, the outputs of the
relation with the original outputs as inputs are simply
the original inputs, which are the same and therefore
also in the relation
C. Is this relation transitive?
Yes - similar to part B, using outputs as inputs and new
outputs as new inputs, every combination of the typical
a, b, and c in the definition of transitive are equal to
each other and also in the relation
D. Is this relation an equivalence relation?
Yes - since the relation is reflexive, symmetric, and
transitive, it is an equivalence relation
-/



/- #3

A binary relation, r, is said to be *anti-symmetric*
if, for all values in its domain, a and b, if r a b
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

Greater than or equal to (>=) is anti-symmetric since
if a >= b and b >= a are both true, then a would have to
equal be since a can't both greater than and less than b
simulatneously
-/


/- #4
A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following
sub-questions. We give you a formal definition of anti
-/

def is_asymmetric
  {α : Type}
  (r : α → α → Prop) : Prop
  := ∀ (a b : α), r a b → ¬ r b a

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here:
Greater than (>) is asymmetric since a number can't be
both greater than and less than another number at the
same time (if x > x - 1 (or any other positive integer),
x - 1 can't be > x)
-/

/- C:

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof):

If r a a is true and r is asymmetric, then r with the
original output as input and the original input as output
would have to be false, but since the outputs and inputs
were the same, this can't happen (r a a can't be true and
false at the same time)
-/

/- D.

Now prove a closely related proposition formally.
Add a comment to each line of your formal proof
so as to construct a good skeleton for a fluent
English language proof.
-/

example
  (α : Type)
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
-- proof by negation
-- unfolding the variable in h
unfold is_asymmetric at h,
-- declaring what we can work with
assume exist,
-- if we have exists then we have witness and proof of witness
cases exist with w Pw,
-- applying the witness above to the definition of symmetric which is assumed for our relation
let contra1 := h w w,
-- using the proof of the witness to discover a contradiction with the definition of symmetric
let contra2 := contra1 Pw,
-- contradiction
contradiction,
end


/- #5
Prove that equality on an inhabited (non-empty) type
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes
that α is inhabited.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
unfold is_asymmetric,
assume all,
let contra1 := all a a,
let contra2 := contra1 rfl,
contradiction,
end

/- Extra credit: What exactly goes wrong in a formal
proof if you drop the "inhibitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).
-/

example (α : Type) : ¬ is_asymmetric (@eq α) :=
begin
unfold is_asymmetric,
assume all,
-- stuck; without any proof of things of type α, we
-- can't do anything with the asymmetric assumption
-- which requires objects of type α to find a contradiction
end



/- #6
Two natural numbers, p and q, are said to be
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop :=
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class.
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
unfold equivalence reflexive symmetric transitive equiv_mod_m,
assume m,
repeat {split},
assume a,
exact rfl,

assume a b h,
rw h,

assume a b c h1 h2,
rw h1,
rw h2,
end



/- #7
Consider the relation, tin_rel, that associates people
with U.S. taxpayer id numbers, which we'll represent as
natural numbers here.

Assume this relation is single-valued. Which of the
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: yes (hopefully); every person should have
a taxpayer id number and every person should only have one
taxpayer id number, no more
-- it's total: no; not every living person has a US
taxpayer id number (e.g. non-US citizens)
-- it's injective (where "): not too familiar with how
US taxpayer id numbers work but i sure hope it's injective
(basically no id number is associated with more than one
person; each person with an id number has a unique id number)
-- it's surjective (where the co-domain is all ℕ): no; there
are infinitely many natural numbers but finite people
-- it's strictly partial: yes; many numbers without associated
people since there are many more numbers than people
-- it's bijective: no; not surjective so can't be bijective
-/



/- #8
Suppose r is the empty relation on the natural
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive: no; since there are no defined inputs
or outputs in the empty relation, it can't map every
natural number (the domain of the function) to itself
-- symmetric: yes; r a b → r b a, but since there is no
"a" or "b" in r (it's empty, after all), then the empty
relation is symmetric by false elimination
-- transitive: yes; similar to the symmetric proof, there
are no a b c values to input to the empty relation r so it
is transitive by false elimination
-/



/- #9
Here's a formal definition of this empty relation.
That there are no constructors given here means there
are no proofs, which is to say that no pair can be
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it,
then prove your assertion. Include English-language
comments on each line to give the essential elements
of a good English language proof.
-/


example : ¬reflexive empty_rel :=
begin
-- rewriting the lean-defined variable name
unfold reflexive,
-- declaring what we can work with
assume h,
-- applying a natural number (any one works) to our empty relation
let x := h 0,
-- nothing in the relation to be reflexive
cases x,
end

example : symmetric empty_rel :=
begin
-- rewriting the lean-defined variable name
unfold symmetric,
-- declaring what we can work with
assume a b h,
-- nothing in the empty relationship, we have cases of h as a proof of false so false elimination
cases h,
end

example : transitive empty_rel :=
begin
-- declaring what we can work with
assume a b c h k,
-- nothing in the empty relationship, we have cases of h as a proof of false so false elimination
cases h,
end

/- #10
A relation, r, is said to have the property of being
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof
that the subset relation on the subsets of any set,
S (of objects of some type), is a partial order.

Pf:
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. reflexive: if a is a subset of b, then b is a subset of a;
since a set by definition can be a subset of itself, the subset
relation is reflexive
2. anti-symmetric: if a is a subset of b, and if b is a subset
of a, then a and b must be equal; since both are subsets of each
other, there can't be any extra values causing one to be bigger than
the other (otherwise the bigger one wouldn't be a subset of the
smaller one), so a and b must be equal
3. transitive: if a is a subset of b and b is a subset of c, then
a must be a subset of c; since being a subset means all values in
set a are in set b and all values in set b are in set c, then all
values in a must be in c so a is a subset of c (like three
concentric circles kinda)

QED.
-/



/- #11
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧)
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for
sets, which states that the complement of a union
of any two sets equals the intersection of their
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a new axiom (called set
extensionality) that states that to prove S = T it
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you
can do by seeing "not," "and," and "or" in place
of complement, conjunction, and disjuction, resp.
-/

example
  (α : Type)
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ :=
begin
ext,
split,

assume h1,
split,
assume xa,
let contra := h1 (or.inl xa),
contradiction,
assume xb,
let contra := h1 (or.inr xb),
contradiction,

assume h1 h2,
apply and.elim h1,
cases h2 with xa xb,
contradiction,
assume thisvariablehasabsolutelynopurposeotherthangettingoutoftheway,
contradiction,
end