from py_ecc.bn128 import is_on_curve, FQ
from py_ecc.fields import field_properties
field_mod = field_properties["bn128"]["field_modulus"]
from hashlib import sha256
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power

b = 3 # for bn128, y^2 = x^3 + 3
seed = "RareSkills"

x = int(sha256(seed.encode('ascii')).hexdigest(), 16) % field_mod 

entropy = 0

vector_basis = []

# modify the code below to generate n points

n = 4

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
x = int(sha256(str(x).encode('ascii')).hexdigest(), 16) % field_mod 
print(vector_basis)
