# albert zeng
# tcf5pw@virginia.edu

from z3 import *

def isValid(c, p):
    s = Solver()
    s.add(Not(p))
    return c + ' is valid' if s.check() == unsat else (c + ' is invalid', s.model())

x, y, z = Bools('x y z')

# c1
c1 = Implies(And(Or(x,y),x), Not(y))
# if x or y is true, and x is also true, then y must be false
# i believe c1 is not valid
print('c1:', isValid('c1', c1))
# because "or" isn't exclusive - both x and y can be true to have "x or y" be true,
# it would not hold that y must be false if x is true (and vice versa) given "x or y"
# e.g. i ate lunch, then i ate dinner, so i ate lunch or dinner today (not exclusively)

# c2
c2 = Implies(And(x,y), And(x,y))
# if x is true and y is true, then x and y together must be true
# i believe c2 is valid
print('c2:', isValid('c2', c2))

# c3
c3 = Implies(And(x,y), x)
# if x and y is true, then x must be true
# i believe c3 is valid
print('c3:', isValid('c3', c3))

# c4
c4 = Implies(And(x,y), y)
# if x and y is true, then y must be true
# i believe c4 is valid
print('c4:', isValid('c4', c4))

# c5
c5 = Implies(Not(Not(x)), x)
# if not-not x is true, then x must be true
# i believe c5 is valid
print('c5:', isValid('c5', c5))

# c6
c6 = Not(And(x, Not(x)))
# it is false that x and not x are true
# i belive that c6 is valid
print('c6:', isValid('c6', c6))

# c7
c7 = Implies(x, Or(x,y))
# if x is true, then x or y is true
# i believe that c7 is valid
print('c7:', isValid('c7', c7))

# c8
c8 = Implies(y, Or(x,y))
# if y is true, then x or y is true
# i believe that c8 is valid
print('c8:', isValid('c8', c8))

# c9
c9 = Implies(And(Implies(x,y), Not(x)), Not(y))
# if x is true, then y is true; but then if x is false, y would be false
# i believe that c9 is not valid
print('c9:', isValid('c9', c9))
# because implies does not equate to equality, it would be incorrect to assume that
# y would be true only if x is true, and similarly, that y would be false only if x
# is false
# e.g. if it rains, then the ground is wet. it didn't rain today, but we did have a 
# water baloon fight, so the ground is still wet

# c10
c10 = Implies(And(Implies(x,y), Implies(y,x)), x==y)
# if x is true, then y is true (and vice versa: if y is true, then x is true); then
# we can conclude that x and y are equivalent (if and only if)
# i believe that c10 is valid
print('c10:', isValid('c10', c10))

# c11
c11 = Implies(x==y, Implies(x,y))
# if x and y are equivalent, then it is true that y is true if x is true
# i believe that c11 is valid
print('c11:', isValid('c11', c11))

# c12
c12 = Implies(x==y, Implies(y,x))
# if x and y are equivalent, then it is true that x is true if y is true
# i believe that c12 is valid
print('c12:', isValid('c12', c12))

# c13
c13 = Implies(And(Or(x,y),Implies(x,z),Implies(y,z)),z)
# if x or y is true, z is true if x is true, and z is true if y is true, then
# z is true
# i believe that c13 is valid
print('c13:', isValid('c13', c13))

# c14
c14 = Implies(And(Implies(x,y), y), x)
# if it is true that y is true if x is true and y is indeed true, then x is true
# i believe that c14 is not valid
print('c14:', isValid('c14', c14))
# similar to c9, this is not valid because implies does not mean equality - it is
# possible for y to be true while x is false, which would invalidate this inference
# rule
# e.g. if it rains, then the ground is wet. the ground is currently wet, but it is
# from the water balloon fight we had; it did not rain today

# c15
c15 = Implies(And(Implies(x,y), x), y)
# if it is true that y is true if x is true and x is indeed true, then y is true
# i believe that c15 is valid
print('c15:', isValid('c15', c15))

# c16
c16 = Implies(And(Implies(x,y), Implies(y,z)), Implies(x,z))
# if it is true that y is true if x is true and also that z is true if y is true,
# then it is true that z is true if x is true
# i believe that c16 is valid
print('c16:', isValid('c16', c16))

# c17
c17 = Implies(Implies(x,y), Implies(y,x))
# if it is true that y is true if x is true, then it is also true that x is true
# when y is true
# i believe that c17 is not valid
print('c17:', isValid('c17', c17))
# similar to c9 and c14, this is not valid because implies does not mean equality
# it is possible for false to imply true (which would satisfy the left side) but
# it is not possible for true to imply false (which would invalidate the right side)
# e.g. if it rains, the ground is wet. but if the ground is wet, it does not mean that
# it rained (we had a water balloon fight and it did not rain today)

# c18
c18 = Implies(Implies(x,y), Implies(Not(y), Not(x)))
# if it is true that y is true if x is true, then it is also true that x is false if
# y is false
# i believe that c18 is valid
print('c18:', isValid('c18', c18))

# c19
c19 = (Not(Or(x,y))) == And(Not(x), Not(y))
# it is true that the negation of x or y together is equivalent to the conjunction
# of the negation of x and the negation of y separately
# i believe that c19 is valid
print('c19:', isValid('c19', c19))

# c20
c20 = (Not(And(x,y))) == Or(Not(x), Not(y))
# it is true that the negation of x and y together is equivalent to the disjunction
# of the negation of x and the negation of y separately
# i believe that c20 is valid
print('c20:', isValid('c20', c20))