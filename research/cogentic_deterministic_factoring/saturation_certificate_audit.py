"""DETFACT-16: independent exact finite roster audit. Standard library only."""
import json
import math
import random


def prime_trial(p):
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p) + 1))


def segmented_roster(k, slots):
    if k < 1 or slots < 1:
        raise ValueError('domain')
    result = []
    def append(p):
        e, q = 1, p
        while q <= k // p:
            e, q = e + 1, q * p
        result.append((p, e, q))
    if k >= 2:
        append(2)
    base = [p for p in range(3, math.isqrt(k) + 1, 2) if prime_trial(p)]
    for lo in range(3, k + 1, 2 * slots):
        hi = min(k, lo + 2 * (slots - 1))
        mark = bytearray(b'\1') * ((hi - lo) // 2 + 1)
        for p in base:
            if p*p > hi:
                break
            first = max(p*p, ((lo+p-1)//p)*p)
            if first % 2 == 0:
                first += p
            for j in range((first-lo)//2, len(mark), p):
                mark[j] = 0
        for j, v in enumerate(mark):
            if v:
                append(lo+2*j)
    return result


def validate(k, roster):
    if k < 1:
        raise ValueError('domain')
    seen = set()
    for p, e, q in roster:
        if not (2 <= p <= k and prime_trial(p)):
            raise ValueError('prime label')
        if p in seen:
            raise ValueError('duplicate')
        seen.add(p)
        if not (1 <= e <= k.bit_length() and q == p**e and q <= k < p*q):
            raise ValueError('maximality')
    if seen != {p for p in range(2, k+1) if prime_trial(p)}:
        raise ValueError('coverage')
    return True


def audit():
    r = dict(schema='DETFACT-16-exact', interval_cases=0, roster_checks=0,
             power_entries=0, streamed_comparisons=0, split_probe_checks=0,
             negative_controls=0)
    rng = random.Random(1601)
    for k in sorted(set(range(1, 257)) | {511,512,513,997,1023,1024,1025,4095,4096,4097,8191,8192,8193,65535,65536,65537}):
        expected = math.lcm(*range(1, k+1))
        r['interval_cases'] += 1
        for slots in [1,7,32,257,8192]:
            roster = segmented_roster(k, slots)
            assert validate(k, roster)
            assert math.prod(q for _,_,q in roster) == expected
            r['roster_checks'] += 1
            r['power_entries'] += len(roster)
        # Independent reference includes the two-adic part, streaming does not.
        m = rng.randrange(1, 1 << 48)
        M = 2*m*expected
        s = (M & -M).bit_length()-1
        odd = M >> s
        odd_m = m >> ((m & -m).bit_length()-1)
        assert s == (m & -m).bit_length() + k.bit_length()-1
        for n,a in [(15,0),(45,3),(77,2),(143,7),(65537,17)]:
            x = pow(a, odd_m, n)
            for p,_,q in roster:
                if p != 2:
                    x = pow(x,q,n)
            assert x == pow(a,odd,n)
            r['streamed_comparisons'] += 1
            for j in range(min(s, 8)+1):
                y = pow(a,odd << j,n)
                assert x == y and math.gcd(abs(x-1),n)==math.gcd(abs(y-1),n)
                r['split_probe_checks'] += 1
                x=x*x%n
    k=30; good=segmented_roster(k,7)
    for bad,reason in [(good[1:],'coverage'),(good+[good[0]],'duplicate'),
                       ([(2,3,7)]+good[1:],'maximality'),
                       ([(2,3,8)]+good[1:],'maximality'),
                       ([(2,5,32)]+good[1:],'maximality'),
                       (good+[(9,1,9)],'prime label'),
                       (good+[(31,1,31)],'prime label')]:
        try: validate(k,bad)
        except ValueError as e: assert str(e)==reason
        else: raise AssertionError('invalid certificate accepted')
        r['negative_controls'] += 1
    # Omitting a prime or using a duplicate may respectively under/overstate LCM.
    assert math.prod(q for _,_,q in good[1:]) < math.lcm(*range(1,k+1))
    assert math.prod(q for _,_,q in good+[good[0]]) > math.lcm(*range(1,k+1))
    return r


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2, sort_keys=True))
