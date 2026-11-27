#!/usr/bin/env python3
"""Replay the minimum-tail rotations on binary position words."""

from itertools import combinations


def valid(word, minimum_tail, omitted):
    anchors = [index for index, bit in enumerate(word) if bit]
    left, right = anchors[0], len(word) - 1 - anchors[-1]
    gaps = [later - earlier for earlier, later in zip(anchors, anchors[1:])]
    return min(left, right) >= minimum_tail and min(gaps) >= omitted + 1


def verify_tail_rotations(maximum_k=20):
    testing_words = 0
    for k in range(6, maximum_k + 1):
        h = k // 2
        for n in range(2 * (h + 2) + 4, 3 * k + 3):
            length = n - 1
            for anchors in combinations(range(1, length - 1), 3):
                left, right = anchors[0], length - 1 - anchors[-1]
                if left > right:
                    continue
                gap = min(b - a for a, b in zip(anchors, anchors[1:]))
                for m in range(h + 1, gap):
                    if left > m:
                        assert 4 * m + 4 <= n - 2 and m < k
                        continue
                    word = [index in anchors for index in range(length)]
                    allowed = sum(
                        valid(word[:cut][::-1] + word[cut:], left, m)
                        for cut in range(1, length)
                    )
                    assert allowed <= n - 2 - 2 * m - left
                    if allowed >= k:
                        assert m <= k - 1
                    testing_words += 1
    print(f"Checked {testing_words} minimum-tail binary words and omission counts.")


def verify_omitted_component_arithmetic():
    for k in range(6, 1000):
        h = k // 2
        assert 2 * (h + 1) > k - 1
        assert 2 * h + 1 >= k
        for m in range(h + 1, k):
            assert 2 * h >= m
            if k % 2 == 0 or m <= k - 2:
                assert 2 * h >= m + 1
                if k >= 15 and m <= k - 4:
                    assert m * (k - m) > 3 * k - 2
    print("Checked the integer connectivity and packing consequences for k=6,…,999.")


if __name__ == "__main__":
    verify_tail_rotations()
    verify_omitted_component_arithmetic()
