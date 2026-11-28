def margins(r, c, j):
    k = 4*r+c
    h = (k+1)//2
    b = h+j
    a = k-b+1
    marks = 2*r+1
    upper = (r+3)*k+1
    return (a+2)*b+a-upper, (marks+2)*b+marks-(b//2-1)-upper

rows = ['F=JJJ','FFJJJ','FFFJJ','FFFJJ','FFFFJ','FFFFJ','FFFFJ']
for c, choices in enumerate(rows, 4):
    for j, choice in enumerate(choices, 1):
        at1 = margins(1,c,j)
        at2 = margins(2,c,j)
        if choice == '=':
            assert at1[0] == at2[0] == 0
        else:
            col = 0 if choice == 'F' else 1
            assert at2[col] >= at1[col] > 0
print('All 35 affine checks pass')
