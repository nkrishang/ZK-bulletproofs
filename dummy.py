import random
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power
from py_ecc.bn128 import is_on_curve, FQ, multiply, add, eq, neg, Z1, curve_order as p
from py_ecc.fields import field_properties
from functools import reduce

field_mod = field_properties["bn128"]["field_modulus"]

def random_field_element():
    return random.randint(0, p)

# Generates a random EC point vector of length n
def generateRandomECPointVec(n):
    b = 3 # for bn128, y^2 = x^3 + 3

    x = random_field_element()

    entropy = 0
    vector_basis = []

    while len(vector_basis) < n:
        while not has_sqrtmod_prime_power((x**3 + b) % field_mod, field_mod, 1):
            # increment x, so hopefully we are on the curve
            x = (x + 1) % field_mod
            entropy = entropy + 1

        # pick the upper or lower point depending on if entropy is even or odd
        y = list(sqrtmod_prime_power((x**3 + b) % field_mod, field_mod, 1))[entropy & 1 == 0]
        point = (FQ(x), FQ(y))
        assert is_on_curve(point, b), "sanity check"
        vector_basis.append(point)

        # new x value
        x = random_field_element()
    
    return vector_basis

def add_points(*points):
    return reduce(add, points, Z1)

### Test

a = 42
b = 31

alpha1 = random_field_element()
alpha2 = random_field_element()
beta1 = random_field_element()
beta2 = random_field_element()

z = random_field_element()

G = generateRandomECPointVec(1)[0]
B = generateRandomECPointVec(1)[0]

L1 = add_points(multiply(G, a), multiply(B, alpha1))
R1 = add_points(multiply(G, a), multiply(B, beta1))
L2 = add_points(multiply(G, b), multiply(B, alpha2))
R2 = add_points(multiply(G, b), multiply(B, beta2))

pi = alpha1 + (alpha2 * z % p) - (beta1 + (beta2 * z % p))

pi_term = multiply(B, pi) if pi >= 0 else neg(multiply(B, -pi))

lhs = add_points(L1, multiply(L2, z))
rhs = add_points(R1, multiply(R2, z), pi_term)

assert eq(lhs, rhs), "invalid equality"

print("accepted")