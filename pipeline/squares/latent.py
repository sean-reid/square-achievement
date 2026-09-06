"""The latent corner of a far reply pair: the cell of the 6 x 6 corner
region that forms three corners of a square with the two replies, when
both replies have a coordinate at least 12. Mirrors farmKey in
formalization/SquareAchievement/Compute/Table.lean.
"""


def farm_relation(o1, o2, box=6, far=12):
    """The hot box cell a far reply pair can farm through, or None.

    A farm square has one box corner t, the two replies as corners,
    and a fourth corner the strategy will block. Every such square
    extends right and down from t with side at least far - box + 1, so
    one reply is aligned with t's row or column and pins t exactly.
    """
    if o1 is None or o2 is None:
        return None
    if max(o1) < far or max(o2) < far:
        return None
    for p, q in ((o1, o2), (o2, o1)):
        if p[0] < box and q[1] == p[1]:
            s = q[0] - p[0]
            b = p[1] - s
            if s >= 1 and 0 <= b < box:
                return ("farm", (p[0], b))
        if p[1] < box and q[0] == p[0]:
            s = q[1] - p[1]
            a = p[0] - s
            if s >= 1 and 0 <= a < box:
                return ("farm", (a, p[1]))
        if p[0] < box and q[1] < box:
            s = p[1] - q[1]
            if s >= 1 and s == q[0] - p[0]:
                return ("farm", (p[0], q[1]))
    return None
