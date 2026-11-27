"""Independent endpoint-rotation sieve, using oriented binary words."""
from itertools import combinations

def check(k,n,m):
    length=n-1
    possible=set()
    for marked in combinations(range(1,length-1),4):
        if min(b-a for a,b in zip(marked,marked[1:])) <= m:
            continue
        word=bytearray(length)
        for mark in marked:
            word[mark]=1
        possible.add(bytes(word))
    def left_pivots(word, accepted):
        # j is the zero-based position of v_j; prefix strictly before it reverses.
        return sum(word[:j][::-1]+word[j:] in accepted for j in range(1,length-1))
    rounds=0
    while True:
        kept={word for word in possible if left_pivots(word,possible)>=k and
                                            left_pivots(word[::-1],possible)>=k}
        if possible==kept:
            return len(kept),len({min(w,w[::-1]) for w in kept}),rounds
        possible=kept
        rounds+=1
if __name__=='__main__':
    for k in range(8,15):
        for n in range(1,3*k+3):
            for m in range(k//2+1,k):
                if 3*(m+1)>n-4 or m*(k-m)>n-4:
                    continue
                oriented,canonical,rounds=check(k,n,m)
                if oriented:
                    print(k,n,m,oriented,canonical,rounds,flush=True)
