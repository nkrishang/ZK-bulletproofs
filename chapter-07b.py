from py_ecc.bn128 import G1, multiply, add, FQ, eq, Z1
from py_ecc.bn128 import curve_order as p
from functools import reduce
import random

def random_element():
    return random.randint(0, p)

def add_points(*points):
    return reduce(add, points, Z1)

def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)

def mod_inner(a, b, p):
    return sum((x * y) % p for x, y in zip(a, b)) % p

def mod_scalar_mul(arr, scalar, p):
    return [(x * scalar) % p for x in arr]

def mod_vec_add(a, b, p):
    return [(x + y) % p for x, y in zip(a, b)]

def mod_vec_mul(a, b, p):
    return [(x * y) % p for x, y in zip(a, b)]

def fold(scalar_vec, u):
    i = 0
    vec = []
    while i < len(scalar_vec):
        vec.append((mod_inner([scalar_vec[i]], [u], p) + mod_inner([scalar_vec[i+1]], [pow(u, -1, p)], p)) % p)
        i += 2
    
    assert len(vec) == len(scalar_vec) / 2
    return vec

def fold_points(point_vec, u):
    i = 0
    vec = []
    while i < len(point_vec):
        vec.append(add_points(multiply(point_vec[i], u), multiply(point_vec[i+1], pow(u, -1, p))))
        i += 2
    
    return vec

def compute_secondary_diagonal(G_vec, a):
    R = Z1
    L = Z1

    for i in range(len(a)):
        if i % 2 == 0:
            R = add_points(R, multiply(G_vec[i], a[i+1]))
        else:
            L = add_points(L, multiply(G_vec[i], a[i-1]))

    return L, R

def compute_secondary_diagonal_scalar(b, a):
    R = 0
    L = 0

    for i in range(len(a)):
        if i % 2 == 0:
            R = (R + (b[i] * a[i+1] % p)) % p
        else:
            L = (L + (b[i] * a[i-1] % p)) % p

    return L, R

def verify(a, b, b_inv, P, G_vec, H_vec, Q):

    assert len(a) == len(b) == len(b_inv) == len(G_vec) == len(H_vec), "vectors must be of same length"

    if len(a) > 1:
        # Compute L and R    
        L_a, R_a = compute_secondary_diagonal(G_vec, a)
        L_b, R_b = compute_secondary_diagonal(H_vec, b)
        L_q, R_q = compute_secondary_diagonal_scalar(b_inv, a)

        L = add_points(L_a, L_b, multiply(Q, L_q))
        R = add_points(R_a, R_b, multiply(Q, R_q))

        # Verifier provided randomness
        u = random_element()

        # Compute P'
        Pprime = add_points(multiply(L, pow(u, 2, p)), P, multiply(R, pow(u, -2, p)))

        # Fold
        aprime = fold(a, u)
        bprime = fold(b, u)
        bprime_inv = fold(b_inv, pow(u, -1, p))

        Gprime = fold_points(G_vec, pow(u, -1, p))
        Hprime = fold_points(H_vec, pow(u, -1, p))

        return verify(aprime, bprime, bprime_inv, Pprime, Gprime, Hprime, Q)
    else:
        return eq(P, add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(Q, mod_inner(a, b_inv, p))))


a = [4, 2, 42, 420]
b = [2, 3, 5, 8]

G_vec = [(FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138)),
     (FQ(6981010364086016896956769942642952706715308592529989685498391604818592148727), FQ(8391728260743032188974275148610213338920590040698592463908691408719331517047)),
     (FQ(15884001095869889564203381122824453959747209506336645297496580404216889561240), FQ(14397810633193722880623034635043699457129665948506123809325193598213289127838)),
     (FQ(6756792584920245352684519836070422133746350830019496743562729072905353421352), FQ(3439606165356845334365677247963536173939840949797525638557303009070611741415))]

H_vec = [(FQ(13728162449721098615672844430261112538072166300311022796820929618959450231493), FQ(12153831869428634344429877091952509453770659237731690203490954547715195222919)),
    (FQ(17471368056527239558513938898018115153923978020864896155502359766132274520000), FQ(4119036649831316606545646423655922855925839689145200049841234351186746829602)),
    (FQ(8730867317615040501447514540731627986093652356953339319572790273814347116534), FQ(14893717982647482203420298569283769907955720318948910457352917488298566832491)),
    (FQ(419294495583131907906527833396935901898733653748716080944177732964425683442), FQ(14467906227467164575975695599962977164932514254303603096093942297417329342836))]

Q = (FQ(11573005146564785208103371178835230411907837176583832948426162169859927052980), FQ(895714868375763218941449355207566659176623507506487912740163487331762446439))

P_inital_commitment = add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(Q, mod_inner(a, b, p)))

assert verify(a, b, b, P_inital_commitment, G_vec, H_vec, Q), "invalid proof"

print("accepted")