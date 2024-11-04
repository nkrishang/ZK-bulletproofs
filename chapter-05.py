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

def mod_inner(a, b, p):
    return sum((x * y) % p for x, y in zip(a, b)) % p

def mod_scalar_mul(arr, scalar, p):
    return [(x * scalar) % p for x in arr]

def mod_vec_add(a, b, p):
    return [(x + y) % p for x, y in zip(a, b)]

# these EC points have unknown discrete logs:
G = [(FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138)),
     (FQ(6981010364086016896956769942642952706715308592529989685498391604818592148727), FQ(8391728260743032188974275148610213338920590040698592463908691408719331517047)),
     (FQ(15884001095869889564203381122824453959747209506336645297496580404216889561240), FQ(14397810633193722880623034635043699457129665948506123809325193598213289127838)),
     (FQ(6756792584920245352684519836070422133746350830019496743562729072905353421352), FQ(3439606165356845334365677247963536173939840949797525638557303009070611741415))]

H = [(FQ(13728162449721098615672844430261112538072166300311022796820929618959450231493), FQ(12153831869428634344429877091952509453770659237731690203490954547715195222919)),
    (FQ(17471368056527239558513938898018115153923978020864896155502359766132274520000), FQ(4119036649831316606545646423655922855925839689145200049841234351186746829602)),
    (FQ(8730867317615040501447514540731627986093652356953339319572790273814347116534), FQ(14893717982647482203420298569283769907955720318948910457352917488298566832491)),
    (FQ(419294495583131907906527833396935901898733653748716080944177732964425683442), FQ(14467906227467164575975695599962977164932514254303603096093942297417329342836))]

B = (FQ(12848606535045587128788889317230751518392478691112375569775390095112330602489), FQ(18818936887558347291494629972517132071247847502517774285883500818572856935411))

# scalar multiplication example: multiply(G, 42)
# EC addition example: add(multiply(G, 42), multiply(G, 100))

# remember to do all arithmetic modulo p
def commit(a, sL, b, sR, alpha, beta, gamma, tau_1, tau_2):

    A = add_points(vector_commit(G, a), vector_commit(H, b), multiply(B, alpha))
    S = add_points(vector_commit(G, sL), vector_commit(H, sR), multiply(B, beta))
    V = add_points(multiply(G1, mod_inner(a,b, p)), multiply(B, gamma))

    T1 = add_points(multiply(G1, (mod_inner(a, sR, p) + mod_inner(b, sL, p)) % p), multiply(B, tau_1))
    T2 = add_points(multiply(G1, mod_inner(sR, sL, p)), multiply(B, tau_2))

    # pass
    return (A, S, V, T1, T2)

## step 0: Prover and verifier agree on G and B

## step 1: Prover creates the commitments
a = [89,15,90,22]
b = [16,18,54,12]
sL = [123, 345, 567, 789]
sR = [3443, 45454, 56565, 76767]
t1 = mod_inner(a, sR, p) + mod_inner(b, sL, p)
t2 = mod_inner(sR, sL, p)

### blinding terms
alpha = 8787878
beta = 2323232
gamma = 1212121
tau_1 = 444444
tau_2 = 57364816

A, S, V, T1, T2 = commit(a, sL, b, sR, alpha, beta, gamma, tau_1, tau_2)

# ## step 2: Verifier picks u
u = random_element()

## step 3: Prover evaluates l(u), r(u), t(u) and creates evaluation proofs
l_u = mod_vec_add(a, mod_scalar_mul(sL, u, p), p)
r_u = mod_vec_add(b, mod_scalar_mul(sR, u, p), p)

term1 = mod_inner(a,b, p)

temp = (mod_inner(a, sR, p) + mod_inner(b, sL, p)) % p
term2 = mod_inner([temp], [u], p)

temp = mod_inner(sR, sL, p)
term3 = mod_inner([temp], [pow(u, 2, p)], p)

# Combine all terms with modular addition
t_u = (term1 + term2 + term3) % p

pi_lr = alpha + mod_inner([beta], [u], p)
pi_t = (gamma + mod_inner([tau_1], [u], p) + mod_inner([tau_2], [pow(u,2,p)], p)) % p

## step 4: Verifier accepts or rejects
assert t_u == mod_inner(l_u, r_u, p), "tu !=〈lu, ru〉"
assert eq(add_points(A, multiply(S, u)), add_points(vector_commit(G, l_u), vector_commit(H, r_u), multiply(B, pi_lr))), "l_u or r_u not evaluated correctly"
assert eq(add_points(multiply(G1, t_u), multiply(B, pi_t)), add_points(V, multiply(T1, u), multiply(T2, pow(u, 2, p)))), "t_u not evaluated correctly"

print("accepted")
