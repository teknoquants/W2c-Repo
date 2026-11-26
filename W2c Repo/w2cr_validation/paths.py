# SPDX-License-Identifier: MIT
# MIT License
#
# Copyright (c) 2026 Roger Cooperman; A.E. Petrunina V.V.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""Enumerate the positively oriented path swaps for factor-two blocking."""
from collections import Counter
from itertools import product


def swaps(bits, direction):
    """Return each oriented square used to sort the two monotone paths."""
    path = [i for i, bit in enumerate(bits) if bit] + [direction]
    final_bits = list(bits)
    final_bits[direction] = 1 - final_bits[direction]
    target = ([direction, direction] if bits[direction] else []) + [
        i for i, bit in enumerate(final_bits) if bit]
    squares = []
    for stop, axis in enumerate(target):
        j = path.index(axis, stop)
        while j > stop:
            point = [0] * len(bits)
            for i in path[:j-1]:
                point[i] += 1
            pair = tuple(sorted(path[j-1:j+1]))
            squares.append((tuple(point), pair))
            path[j-1], path[j] = path[j], path[j-1]
            j -= 1
    assert path == target
    return squares


def periodic_counts(d):
    # Translation by 2 Z^d is free on roots. A column is determined by the
    # orientation and parity of its lower vertex. Each matching offset occurs
    # at exactly one root incident to a specified translated square.
    columns = Counter()
    rows = []
    for bits in product(range(2), repeat=d):
        for axis in range(d):
            terms = swaps(bits, axis)
            rows.append(len(terms))
            for point, pair in terms:
                columns[tuple(x%2 for x in point), pair] += 1
    return dict(d=d, max_swaps=max(rows), max_incidence=max(columns.values()),
                row_histogram=dict(sorted(Counter(rows).items())),
                column_histogram=dict(sorted(Counter(columns.values()).items())),
                schur_squared=max(rows)*max(columns.values()))


def finite_counts(sides):
    """Enumerate actual oriented fine edges and incident squares; no wrap."""
    columns = Counter()
    largest = 0
    for vertex in product(*(range(L+1) for L in sides)):
        bits = tuple(x%2 for x in vertex)
        root = tuple(x-b for x,b in zip(vertex,bits))
        for axis,L in enumerate(sides):
            if vertex[axis] == L:
                continue
            terms = swaps(bits, axis)
            largest = max(largest,len(terms))
            for offset, pair in terms:
                sq = tuple(x+y for x,y in zip(root,offset))
                assert all(0<=v<=sides[i]-(i in pair) for i,v in enumerate(sq))
                columns[sq,pair] += 1
    return largest,max(columns.values())
