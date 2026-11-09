#!/usr/bin/env python3
"""Bounded research probe, not a certified numerical backend.

Only Python's standard library is used. Counts describe executed scalar source
operations; allocation, scalar bit complexity and wall time are not inferred.
"""
import argparse
from collections import Counter
from decimal import Decimal, localcontext
import json
import math
import platform

BACKENDS = ("pose", "complex", "lorentz", "spin")
MAX_STEPS = 64


class Arithmetic:
    def __init__(self, carrier):
        self.carrier = carrier
        self.count = Counter()

    def scalar(self, x):
        return Scalar(self.carrier(x), self)

    def rational(self, text):
        parts = text.split("/")
        # Input conversion is separate from backend arithmetic observations.
        n = self.carrier(parts[0])
        return Scalar(n / self.carrier(parts[1]) if len(parts) == 2 else n, self)


class Scalar:
    def __init__(self, value, arithmetic):
        self.value, self.arithmetic = value, arithmetic

    def operation(self, other, name, f):
        v = other.value if isinstance(other, Scalar) else self.arithmetic.carrier(other)
        self.arithmetic.count[name] += 1
        return Scalar(f(self.value, v), self.arithmetic)

    def __add__(self, other): return self.operation(other, "add", lambda x, y: x + y)
    __radd__ = __add__
    def __sub__(self, other): return self.operation(other, "sub", lambda x, y: x - y)
    def __rsub__(self, other): return (-self) + other
    def __mul__(self, other): return self.operation(other, "mul", lambda x, y: x * y)
    __rmul__ = __mul__
    def __truediv__(self, other): return self.operation(other, "div", lambda x, y: x / y)
    def __neg__(self):
        self.arithmetic.count["neg"] += 1
        return Scalar(-self.value, self.arithmetic)
    def sqrt(self):
        self.arithmetic.count["sqrt"] += 1
        return Scalar(self.value.sqrt() if isinstance(self.value, Decimal) else math.sqrt(self.value), self.arithmetic)


def flatten(xs):
    if isinstance(xs, Scalar):
        yield xs
    else:
        for x in xs:
            yield from flatten(x)


def cadd(a, b): return a[0] + b[0], a[1] + b[1]
def cneg(a): return -a[0], -a[1]
def conj(a): return a[0], -a[1]
def cmul(a, b): return a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0]
def norm2(a): return a[0]*a[0] + a[1]*a[1]
def cdiv(a, b):
    n = norm2(b)
    t = cmul(a, conj(b))
    return t[0]/n, t[1]/n


def constants(p):
    c = p[0][0].arithmetic
    return c.scalar(0), c.scalar(1)


def valid_pose(p):
    z, u = p
    # Diagnostic policy only. Input phases are exact rational unit-circle data;
    # rounded phases need not have exactly unit squared norm.
    if not (z[0].value*z[0].value + z[1].value*z[1].value < 1):
        raise ValueError("disk point outside strict domain")


def mmul(a, b, complex_values=False):
    add, mul = (cadd, cmul) if complex_values else (lambda x,y:x+y, lambda x,y:x*y)
    n = len(a)
    out = []
    for i in range(n):
        row = []
        for j in range(n):
            v = mul(a[i][0], b[0][j])
            for k in range(1, n):
                v = add(v, mul(a[i][k], b[k][j]))
            row.append(v)
        out.append(row)
    return out


def blade_product(a, b):
    # Ordered basis e0,e1,e2 with e0²=-1,e1²=e2²=+1.
    sign = -1 if sum((b & ((1 << i)-1)).bit_count() for i in range(3) if a & (1 << i)) % 2 else 1
    if a & b & 1:
        sign = -sign
    return a ^ b, sign


def gp(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            k, sign = blade_product(i, j)
            v = x*y if sign == 1 else -(x*y)
            out[k] = out[k] + v if k in out else v
    return out


def reverse(r):
    return {i: (-x if (i.bit_count()*(i.bit_count()-1)//2) % 2 else x) for i,x in r.items()}


def spin_inverse(r):
    n = gp(r, reverse(r))[0]
    if not n.value > 0:
        raise ValueError("nonpositive rounded spin norm")
    return {i:x/n for i,x in reverse(r).items()}


def encode(name, p):
    valid_pose(p)
    a, u = p
    z, one = constants(p)
    if name == "pose":
        return p
    if name == "complex":
        return [[u, a], [cmul(conj(a), u), (one, z)]]
    gap = one - norm2(a)
    if name == "lorentz":
        x, y = a
        b = [[(one+norm2(a))/gap, 2*x/gap, 2*y/gap],
             [2*x/gap, one+2*x*x/gap, 2*x*y/gap],
             [2*y/gap, 2*x*y/gap, one+2*y*y/gap]]
        rot = [[one,z,z],[z,u[0],-u[1]],[z,u[1],u[0]]]
        return mmul(b, rot)
    if name == "spin":
        # Local half-angle lift; the u=-1 branch chooses positive sine.
        c = ((one + u[0])/2).sqrt()
        s = u[1]/(2*c) if c.value != 0 else one
        g = gap.sqrt()
        return gp({0:one/g,3:a[0]/g,5:a[1]/g}, {0:c,6:-s})
    raise ValueError(name)


def compose(name, p, q):
    # Right operand acts first, as in the native library.
    if name == "pose":
        a,u = p
        b,v = q
        zero,one = constants(p)
        ub = cmul(u,b)
        d = cadd((one,zero), cmul(conj(a),ub))
        return cdiv(cadd(a,ub),d), cmul(cmul(cdiv(conj(d),d),u),v)
    if name in ("complex", "lorentz"):
        return mmul(p,q,name == "complex")
    if name == "spin": return gp(p,q)
    raise ValueError(name)


def inverse(name, p):
    if name == "pose": return cneg(cmul(conj(p[1]),p[0])), conj(p[1])
    if name == "complex":
        # Adjugate is sufficient projectively; no determinant normalization.
        return [[p[1][1], cneg(p[0][1])], [cneg(p[1][0]),p[0][0]]]
    if name == "lorentz":
        return [[(-p[j][i] if (i==0) != (j==0) else p[j][i]) for j in range(3)] for i in range(3)]
    if name == "spin": return spin_inverse(p)
    raise ValueError(name)


def decode_frame(x, e):
    d = x[0]+1
    return (x[1]/d,x[2]/d), ((e[1]*d-x[1]*e[0])/(d*d), (e[2]*d-x[2]*e[0])/(d*d))


def decode(name, p):
    if name == "pose":
        a,u = p
        g = (1-norm2(a))/2
        return a,(g*u[0],g*u[1])
    if name == "complex":
        det = cadd(cmul(p[0][0],p[1][1]), cneg(cmul(p[0][1],p[1][0])))
        h = cdiv(det,cmul(p[1][1],p[1][1]))
        return cdiv(p[0][1],p[1][1]), (h[0]/2,h[1]/2)
    if name == "lorentz":
        return decode_frame([p[i][0] for i in range(3)], [p[i][1] for i in range(3)])
    if name == "spin":
        one = p[0].arithmetic.scalar(1)
        inv = spin_inverse(p)
        x,e = (gp(gp(p,{i:one}),inv) for i in (1,2))
        return decode_frame([x[i] for i in (1,2,4)], [e[i] for i in (1,2,4)])
    raise ValueError(name)


def workload(n):
    if not 0 <= n <= MAX_STEPS:
        raise ValueError("workload exceeds fixed 64-step resource cutoff")
    cycle = ((("1/8","1/16"),("3/5","4/5")),
             (("-1/10","1/12"),("4/5","-3/5")),
             (("0","-1/9"),("0","1")))
    return [cycle[i % len(cycle)] for i in range(n)]


def parse_pose(c, p):
    return tuple(tuple(c.rational(x) for x in part) for part in p)


def observation_values(obs):
    return [x.value for x in flatten(obs)]


def compute(name, n, initial, carrier, reuse=False, diagnostics=False):
    c = Arithmetic(carrier)
    inputs = [parse_pose(c,p) for p in workload(n)]
    start = parse_pose(c,initial)
    if reuse:
        cache = {}
        increments = []
        for key, p in zip(workload(n), inputs):
            if key not in cache:
                cache[key] = encode(name, p)
            increments.append(cache[key])
    else:
        increments = [encode(name,p) for p in inputs]
    state = encode(name,start)
    conversion = dict(c.count)
    c.count.clear()
    for inc in increments:
        state = compose(name,inc,state)
    composition = dict(c.count)
    c.count.clear()
    obs = observation_values(decode(name,state))
    observation = dict(c.count)
    costs = {"conversion":conversion,"composition":composition,"decode":observation}
    if diagnostics:
        # Diagnostics use the stored coordinates, outside the backend event count.
        if name == "lorentz":
            m = [[x.value for x in row] for row in state]
            defect = max(abs(sum((-1 if k==0 else 1)*m[k][i]*m[k][j] for k in range(3))
                             - ((-1 if i==0 else 1) if i==j else 0))
                         for i in range(3) for j in range(3))
            diag = {"lorentz_gram_max_absolute_defect":str(defect)}
        elif name == "spin":
            r = {i:x.value for i,x in state.items()}
            diag = {"spin_unit_norm_absolute_defect":str(abs(r[0]**2-r[3]**2-r[5]**2+r[6]**2-1))}
        elif name == "pose":
            u = state[1]
            diag = {"phase_unit_norm_absolute_defect":str(abs(u[0].value**2+u[1].value**2-1))}
        else:
            diag = {}
        return obs, costs, diag
    return obs, costs


def errors(actual, reference):
    a = [Decimal.from_float(x) for x in actual]
    point = ((a[0]-reference[0])**2+(a[1]-reference[1])**2).sqrt()
    frame = ((a[2]-reference[2])**2+(a[3]-reference[3])**2).sqrt()
    norm = (reference[2]**2+reference[3]**2).sqrt()
    gap = 1-reference[0]**2-reference[1]**2
    actual_gap = 1-a[0]**2-a[1]**2
    # Scaled tangent sensitivity diagnostic, not a global distance bound.
    return {"point_absolute":str(point), "frame_relative":str(frame/norm),
            "point_gap_scaled":str(2*point/gap), "inside_disk":actual_gap>0}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    results = {"python":platform.python_version(), "float_mantissa":53,
               "reference_decimal_precision":80, "crosscheck_decimal_precision":120,
               "seed":None, "max_steps":MAX_STEPS,
               "renormalization":"none; spin inverse uses computed reverse/norm", "cases":[], "reuse":[]}
    with localcontext() as context:
        context.prec = 80
        for k in (0, 8, 20, 40, 50):
            radius = Decimal(0) if k == 0 else 1-Decimal(2)**(-k)
            initial = ((str(radius*Decimal(3)/5),str(radius*Decimal(4)/5)),("4/5","3/5"))
            for n in (0,1,8,64):
                ref,_ = compute("pose",n,initial,Decimal)
                with localcontext() as crosscheck:
                    crosscheck.prec = 120
                    ref120,_ = compute("pose",n,initial,Decimal)
                    reference_change = str(max(abs(x-y) for x,y in zip(ref,ref120)))
                for name in BACKENDS:
                    record = {"backend":name,"boundary_bits":k,"steps":n,
                              "reference_precision_change_max":reference_change}
                    try:
                        actual,cost,diagnostics = compute(name,n,initial,float,diagnostics=True)
                        if not all(math.isfinite(x) for x in actual):
                            raise ValueError("nonfinite observation")
                        record.update(errors(actual,ref))
                        record["scalar_events"] = cost
                        record["diagnostics"] = diagnostics
                        # A second high-precision algorithm checks implementation agreement.
                        high,_ = compute(name,n,initial,Decimal)
                        record["reference_agreement_max"] = str(max(abs(x-y) for x,y in zip(high,ref)))
                    except (ValueError,ArithmeticError) as exc:
                        record["failure"] = str(exc)
                    results["cases"].append(record)
        initial = (("1/3","0"),("0","1"))
        for name in BACKENDS:
            a,cost = compute(name,64,initial,float)
            b,cached = compute(name,64,initial,float,reuse=True)
            results["reuse"].append({"backend":name,"steps":64,"unique_increments":3,
                                     "observations_identical":a==b,
                                     "uncached":cost,"cached":cached})
    with open(args.output,"w") as f:
        json.dump(results,f,indent=2,sort_keys=True)
        f.write("\n")


if __name__ == "__main__":
    main()
