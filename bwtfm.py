def suffixArray(s):
    """ Given T return suffix array SA(T). We use Python's sorted
    function here for simplicity, but we can do better. """
    # Empty suffix '' plays role of $.
    satups = sorted([(s[i:], i) for i in xrange(0, len(s)+1)])
    # Extract and return just the offsets
    return map(lambda x: x[1], satups)

def bwt(t):
    """ Given T, returns BWT(T), by way of the suffix array. """
    bw = []
    for si in suffixArray(t):
        if si == 0:
            bw.append('$')
        else:
            bw.append(t[si-1])
    return ''.join(bw) # return string-ized version of list bw

def rankBwt(bw):
    """ Given BWT string bw, returns a parallel list of B-ranks. Also
    returns tots, a mapping from characters to # times the
    character appears in BWT. """
    tots = dict()
    ranks = []
    for c in bw:
        if c not in tots:
            tots[c] = 0
        ranks.append(tots[c])
        tots[c] += 1
    return ranks, tots

def firstCol(tots):
    """ Return a map from characters to the range of cells in the first
    column containing the character. """
    first = {}
    totc = 0
    for c, count in sorted(tots.iteritems()):
        first[c] = (totc, totc + count)
        totc += count
    return first

def reverseBwt(bw):
    """ Make T from BWT(T) """
    ranks, tots = rankBwt(bw)
    print 'ranks', ranks, tots
    first = firstCol(tots)
    print 'first', first
    rowi = 0
    t = "$"
    while bw[rowi] != '$':
        c = bw[rowi]
        print rowi, c, first[c], ranks[rowi]
        t = c + t
        rowi = first[c][0] + ranks[rowi]
    return t
