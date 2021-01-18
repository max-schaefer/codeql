function f(x) {
    return x.p;
}

var o = {
    p: 0 // candidateRep: rhs (member p (parameter 0 (member exports *)))
}

f(o);

module.exports = f;
