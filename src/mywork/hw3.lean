-- albert zeng
-- tcf5pw@virginia.edu

/- #1: Logic to English 

Read through the new material in 09_20_22_inference_rules.lean, which
starts on line 264. After reviewing our all balls blue example, it then
presents an English-language rendition of our "demonstration" that if 
all balls are blue and if b1 and b2 are balls then b1 is blue and b2 
is blue. Compare the English language proof with the formal version, 
paying attention to how we named and specified the proof that all balls
are blue. 

Continue reading through our formalized version of the story that 
everyone is mortal and so is Socrates so Socrates is mortal. Now 
write an English-language version of the proof, using the model from 
the earlier case of "all balls blue." Don't just do it mindlessly: 
really think about what you're saying with each word in your proof. 
See how the English presents the "story" of the formal proof in more
natural, human, terms.

ANSWER HERE:
First, we define the necessary variables: we have Socrates, who is a
person, and all people in general, who are mortals. We have a proof
that all people in general are mortals, which we can then apply to any
arbitrary but specific person -- in this case, Socrates. By applying
our generalized proof that every person is mortal to a specific person,
Socrates, we can obtain a more specific proof that Socrates himself is
mortal.

-/


/- #2: English to Logic 
Formally model this natural-language "logic story" in Lean, using
the material we covered in the lecture notes as a model. Here's the
story.

If one person likes a second, and the second likes a third, 
then the first is jealous of the third. Furthermore, Ed, Hannah, 
and Mel are people; Ed likes Hannah; and Hannah likes Mel. 

Write, and use #check to check, an expression that proves that Ed 
is jealous of Mel. 

To do so, uncomment the following block of expressions then fill 
in blanks to complete this task.
-/

-- Uncomment this block to answer the question
variable Person : Type
variable Likes : Person → Person → Prop       -- a predicate with two Person arguments
variable Jealous : Person → Person → Prop      -- same thing here  
variable Triangle :       -- note definition extends to next line
  ∀ (p1 p2 p3 : Person), Likes p1 p2 → Likes p2 p3 → Jealous p1 p3 
variables ed hannah mel : Person
variable likes_ed_hannah : Likes ed hannah
variable likes_hannah_mel : Likes hannah mel
-- Finally write and use #check to check an expression that proves that ed is 
-- jealous of mel.
-- To ANSWER, fill in the _ with your expression. 
-- HINT "Apply" what you know.

#check (Triangle ed hannah mel)


/- #3: Proofing a propositions involving ∀ and ∨

Write an English-language  proof of the following proposition, using
the methods of inference we've covered: ∀ (P Q : Prop), P ∧ Q → Q ∨ P. 

Do read that proposition carefully, please. You don't need to write a
long proof. Keep it concise. Identiy the inference rules you use.

ANSWER HERE:
Suppose P and Q are two arbitrary propositions. Assuming that we have
a proof of the conjunction of P and Q, we can apply the left and right
and-elimination rules to obtain proofs of P and Q separately. Then,
with individual proofs of both P and Q (even though, for the purposes
of this problem, we only need one of them), we can use either the left
or-introduction rule on Q or the right or-introduction rule on P to
obtain the desired proof of the disjunction of Q and P.

-/


/- 
Model the following logic story formally. Everyone knows someone who 
knows someone who knows everyone.

Note: As you've likely defined Person as a type in answering question
#2, you don't need to do it again here. Comment out the definition we
give you if it's redundant with your answer above. Give your answer
by writing the formalized proposition in place of the _ that follows.
You may (and probably should) break up your expression over several
lines, using line breaks and indentation to make the answer readable.
-/

-- variable Person : Type
variable Knows : Person → Person → Prop
def answer : Prop := 
    ∀ (p1 p4 : Person),
    ∃ (p2 p3 : Person),
    Knows p1 p2 →
    Knows p2 p3 →
    Knows p3 p4