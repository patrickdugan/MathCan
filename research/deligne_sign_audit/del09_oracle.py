"""DEL-09: exact finite-field witnesses for parameter descent and projective charts.

These finite computations are diagnostic shadows of the scheme theorems in
ProjectiveQuasiFinite.lean and FiniteParameterDescent.lean. Actual generic
Bertini smoothness and Katz A.5 stay as explicit geometric premises.
"""
from research.deligne_sign_audit.prime_power_fourier import FIELDS


def common_subfield_degree(field, coefficients):
    """Least e|m such that all coefficients are in F_(p^e) inside F_(p^m)."""
    coeffs = tuple(coefficients)
    if any(not 0 <= c < field.q for c in coeffs):
        raise ValueError("coordinate outside ambient extension")
    m = field.degree
    for e in range(1, m + 1):
        if m % e != 0:
            continue
        if all(field.pow(c, field.p ** e) == c for c in coeffs):
            members = tuple(x for x in range(field.q)
                            if field.pow(x, field.p ** e) == x)
            assert len(members) == field.p ** e
            assert all(c in members for c in coeffs)
            return e, len(members)
    raise AssertionError("the ambient finite field must contain all coordinates")


def polynomial_open_frobenius_gap(field):
    """D(X^p-X) has p^m-p points over F_(p^m) for m>1;
    every F_p point lies in its complementary zero locus."""
    base_zero = tuple(x for x in range(field.p)
                      if field.sub(field.pow(x, field.p), x) == 0)
    extension_open = tuple(x for x in range(field.q)
                           if field.sub(field.pow(x, field.p), x) != 0)
    return base_zero, extension_open


def quadratic_regular_function(field, x, a, b):
    """Extra graph coordinate B(x)=a*x^2+b."""
    return field.add(field.mul(a, field.mul(x, x)), b)


def projective_chart_graph(field, a, b):
    """Represent the affine graph point as [1:x:B(x)]."""
    return tuple((1, x, quadratic_regular_function(field, x, a, b))
                 for x in range(field.q))


def projective_graph_fibers(field, a, b):
    """The standard projective chart with first coordinate=1
    has singleton fibers on the graph, since x is retained."""
    points = projective_chart_graph(field, a, b)
    inverse = {}
    for x, point in enumerate(points):
        inverse.setdefault(point, []).append(x)
    return inverse


def affine_chart_contains(point):
    """Whether a projective coordinate tuple admits a representative
    with first coordinate 1. Only the nonvanishing status matters."""
    if not point:
        raise ValueError("empty projective coordinates")
    return point[0] != 0


def injective_graph_certificate(field, a, b):
    fibers = projective_graph_fibers(field, a, b)
    assert len(fibers) == field.q
    assert all(len(v) == 1 for v in fibers.values())
    assert all(affine_chart_contains(p) for p in fibers)
    return len(fibers), max(map(len, fibers.values()), default=0)


def omit_base_coordinate_mutant(field):
    """The map [1:x^p-x:0] collapses the entire F_p rational locus.
    It is not a replacement for a closed immersion of schemes."""
    pts = tuple((1, field.sub(field.pow(x, field.p), x), 0)
                for x in range(field.p))
    return len(set(pts)), len(pts)


def affine_normalization(field, coeffs, scalar):
    """Scaling [linear coefficients, c] by lambda != 0."""
    if scalar == 0:
        raise ValueError("fixed coefficient chart requires nonzero scalar")
    inv = field.inv(scalar)
    return tuple(field.mul(c, inv) for c in coeffs)


def source_geometry_tangency_mutant(field):
    """The hypersurface xy+1=0 is smooth in A² but its intersection
    with y=x-2 has a double point at x=1, in any characteristic."""
    one, two = 1, field.add(1, 1)
    y = field.sub(one, two)
    equation = field.add(field.mul(one, y), one)
    gradient = (y, one)
    tangent_line = field.add(y, field.sub(one, two))
    # derivative of x*(x-2)+1 at x=1 is 2*(1-1)=0
    derivative = field.sub(field.add(one, one), two)
    return equation == 0, any(gradient), tangent_line == 0, derivative == 0


def validate_ambient_field(name):
    field = FIELDS[name]
    elements = tuple(range(field.q))
    assert all(field.pow(x, field.q) == x for x in elements)
    return field
