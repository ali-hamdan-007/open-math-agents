"""Check the sharp constructions and independently exhaust all feasible k<=7."""
from itertools import product


def statistics(weights):
    degrees = [s + weights[i-1] + weights[(i+1)%7] - 1
               for i, s in enumerate(weights)]
    smallest = min(range(7), key=degrees.__getitem__)
    k = degrees[smallest] if weights[smallest] > 1 else min(
        degrees[:smallest] + degrees[smallest+1:])
    even = max(weights[(i-2)%7] + weights[(i+2)%7] for i in range(7))
    return k, even


def example(k):
    h, r = divmod(k, 3)
    if r == 0:
        return (h+1, h, h, h+1, 2*h-1, 2*h, 2*h-1)
    if r == 1:
        return (h+1, h, h+1, h+1, 2*h, 2*h, 2*h)
    return (h+1, h+1, h+1, h+1, 2*h+1, 2*h+1, 2*h+1)


if __name__ == '__main__':
    feasible = [2, *range(4, 1001)]
    for k in feasible:
        weights = example(k)
        actual_k, even = statistics(weights)
        assert actual_k == k and even <= k
        assert sum(weights) == (10*k+1)//3
    # For k<=7 each weight is <=6 because its even-class partner is nonempty.
    maxima = {}
    for weights in product(range(1, 7), repeat=7):
        k, even = statistics(weights)
        if even <= k <= 7:
            maxima[k] = max(maxima.get(k, 0), sum(weights))
    assert maxima == {2:7, 4:13, 5:17, 6:20, 7:23}
    print('All rounded-bound constructions checked up to k=1000.')
    print('Exhaustive maxima for k<=7:', dict(sorted(maxima.items())))
