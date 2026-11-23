"""Predeclared joint endpoint and shot/systematic uncertainty."""
from math import sqrt

import numpy as np
from scipy.stats import norm

SHOTS = 2048
SAMPLING_SEED = 991040
SYSTEMATIC = .01
JOINT_FLOOR = .80


def wilson(k, n, alpha=.05):
    z = norm.isf(alpha / 2)
    p = k/n
    d = 1 + z*z/n
    center = (p + z*z / (2*n))/d
    radius = z*sqrt(p*(1-p)/n + z*z/(4*n*n))/d
    return [max(0., center-radius), min(1., center+radius)]


def model_endpoints(p, label):
    positive, negative = map(float, p[[0, 8]])
    ret = positive + negative
    joint = negative if label == "AB" else positive
    return {"return": ret, "joint_correct_and_return": joint,
            "conditional_correct": joint/ret if ret else 0.,
            "conditional_Y": (positive-negative)/ret if ret else 0.,
            "return_and_positive_Y": positive}


def from_counts(counts, label):
    count = np.asarray(counts)
    shots = int(count.sum())
    ret = int(count[0] + count[8])
    joint = int(count[8] if label == "AB" else count[0])
    return {**model_endpoints(count / shots, label), "shots": shots,
            "joint_successes": joint, "return_successes": ret,
            "joint_wilson_95": wilson(joint, shots),
            "return_wilson_95": wilson(ret, shots),
            "conditional_correct_wilson_95": wilson(joint, ret) if ret else [0., 1.]}


def primary_interval(rows):
    intervals = [wilson(r["joint_successes"], r["shots"], alpha=.025) for r in rows]
    return [max(0., np.mean([v[0] for v in intervals])-SYSTEMATIC),
            min(1., np.mean([v[1] for v in intervals])+SYSTEMATIC)]


def commuting_interval(a, b):
    first, second = [wilson(row["counts"][0], SHOTS, alpha=.025) for row in (a, b)]
    return [max(-1., first[0]-second[1]-2*SYSTEMATIC),
            min(1., first[1]-second[0]+2*SYSTEMATIC)]
