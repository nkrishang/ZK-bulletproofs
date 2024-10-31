from py_ecc.bn128 import G1, multiply, add, FQ, eq, Z1
from py_ecc.bn128 import curve_order as p
import numpy as np
from functools import reduce
import random

def random_element():
    return random.randint(0, p)

def add_points(*points):
    return reduce(add, points, Z1)

# if points = G1, G2, G3, G4 and scalars = a,b,c,d vector_commit returns
# aG1 + bG2 + cG3 + dG4
def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)

# these EC points have unknown discrete logs:
G_vec = [(FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138)),
     (FQ(6981010364086016896956769942642952706715308592529989685498391604818592148727), FQ(8391728260743032188974275148610213338920590040698592463908691408719331517047)),
     (FQ(15884001095869889564203381122824453959747209506336645297496580404216889561240), FQ(14397810633193722880623034635043699457129665948506123809325193598213289127838)),
     (FQ(6756792584920245352684519836070422133746350830019496743562729072905353421352), FQ(3439606165356845334365677247963536173939840949797525638557303009070611741415))]

# return a folded vector of length n/2 for scalars
def fold(scalar_vec, u):
    pass

# return a folded vector of length n/2 for points
def fold_points(point_vec, u):
    pass

# return (L, R)
def compute_secondary_diagonal(G_vec, a):
    pass

a = [4,2,42,420]

P = vector_commit(G_vec, a)

L1, R1 = compute_secondary_diagonal(G_vec, a)
u1 = random_element()
aprime = fold(a, u1)
Gprime = fold_points(G_vec, pow(u1, -1, p))

L2, R2 = compute_secondary_diagonal(Gprime, aprime)
u2 = random_element()
aprimeprime = fold(aprime, u2)
Gprimeprime = fold_points(Gprime, pow(u2, -1, p))

assert len(Gprimeprime) == 1 and len(aprimeprime) == 1, "final vector must be len 1"
assert eq(vector_commit(Gprimeprime, aprimeprime), add_points(multiply(L2, pow(u2, 2, p)), multiply(L1, pow(u1, 2, p)), P, multiply(R1, pow(u1, -2, p)), multiply(R2, pow(u2, -2, p)))), "invalid proof"
