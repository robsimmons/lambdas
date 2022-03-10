const s = require('jAgda.simplify');
const index = require('jAgda.Data.List.Relation.Unary.Any')["Any"];

window.s = s;

const _const = {
    a: () => "a",
    b: () => "b",
    f: () => "f",
    g: () => "g"
}
function decodeConst(c) {
    return c(_const);
}

function encodeConst(c) {
    switch(c) {
    case "a": return s["const"].a;
    case "b": return s["const"].b;
    case "f": return s["const"].f;
    case "g": return s["const"].g;
    }
}

const _index = {
    "here": (_) => 0,
    "there": (x) => 1+decodeIndex(x),
}
function decodeIndex(x) {
    console.log(x);
    return x(_index);
}
function encodeIndex(x) {
    if (x == 0) {
	return index.here(null);
    } else {
	return index.there(encodeIndex(x-1));
    }
}

function decodeTau(tau) {
    return tau;
}
function encodeTau(tau) {
    return tau;
}


const _head = {
    "var": (x) => decodeIndex(x),
    "con": (c) => decodeConst(c),
    "free": (u) => ({ tag: "free", index: decodeIndex(u) }),
}
function decodeHead(head) {
    return head(_head);
}
function encodeHead(head) {
    if (typeof(head) === "number") {
	return s.head["var"](encodeIndex(head));
    } else if (typeof(head) === "string") {
	return s.head["con"](encodeConst(head));
    } else {
	return s.head["free"](encodeIndex(head.index));
    }
}

const _term = {
    "lambda": body => ({ body: decodeTerm(body), tag: "lambda" }),
    "root": (tau, head, spine) => ({ tau: decodeTau(tau), head: decodeHead(head), spine: decodeSpine(spine), tag: "root" }),
    "mvar": (uh, u, subst) => ({ uh, u: decodeIndex(u), subst: decodeSubst(subst), tag: "mvar" }),
    "hole": () => ({ tag: "hole" }),
}
function decodeTerm(term) {
    console.log(term);
    return term(_term);
}
function encodeTerm(term) {
    console.log(term);
    switch (term.tag) {
    case "lambda": return s.term["lambda"](encodeTerm(term.body));
    case "root": return s.term["root"](encodeTau(term.tau))(encodeHead(term.head))(encodeSpine(term.spine));
    case "mvar": return s.term["mvar"](term.uh)(encodeIndex(term.u))(encodeSubst(term.subst));
    case "hole": return s.term["hole"];
    }
}

const _spine = {
    "nil": () => [],
    "cons": (term, spine) => ([decodeTerm(term)].concat(decodeSpine(spine))),
}
function decodeSpine(spine) {
    return spine(_spine);
}
function encodeSpine(spine) {
    if (spine.length == 0) {
	return s.spine["nil"];
    }
    return s.spine["cons"](encodeTerm(spine[0]))(encodeSpine(spine.slice(1)));
}

function decodeSubst(subst) {
    return subst;
}
function encodeSubst(subst) {
    return subst;
}


const _eqn = {
    "unifyTerm": (gamma, tau, t1, t2) => ({ tag: "term", gamma, tau, t1: decodeTerm(t1), t2: decodeTerm(t2) }),
    "unifyMvar": (gamma, u, t1) => ({ tag: "mvar", gamma, u: u, t1: decodeTerm(t1)}),
}
function decodeEqn(eqn) {
    return eqn(_eqn);
}
function encodeEqn(eqn) {
    switch (eqn.tag) {
    case "term": return s.eqn["unifyTerm"](eqn.gamma)(eqn.tau)(encodeTerm(eqn.t1))(encodeTerm(eqn.t2));
    case "mvar": return s.eqn["unifyMvar"](eqn.gamma)(eqn.u)(encodeTerm(eqn.t1));
    }
}

const _simplified = {
    "stalled": constraints => ({ tag: "stalled", constraints: constraints.map(decodeEqn)}),
    "progress": constraints => ({ tag: "progress", constraints: constraints.map(decodeEqn)}),
    "failure": () => ({ tag: "failure" }),
    "assign": (psi, u, tm, constraints) => ({ tag: "assign", u: decodeIndex(u), tm: decodeTerm(tm), constraints: constraints.map(decodeEqn) }),
}
function decodeSimplified(simplified) {
    return simplified(_simplified);
}

window.decodeConst = decodeConst
window.encodeConst = encodeConst
window.decodeTerm = decodeTerm
window.encodeTerm = encodeTerm

let x = s.problem1;

window.f = () => {
    const ea = document.createElement("div");
    ea.innerHTML = JSON.stringify(x.map(decodeEqn));
    document.body.append(ea);

    const result = s["simplify-something"](s.problem1Delta)(x);
    const e = document.createElement("div");
    const decoded = decodeSimplified(result);
    e.innerHTML = JSON.stringify(decoded);
    document.body.append(e);
    if (decoded.tag === "progress") {
	x = decoded.constraints.map(encodeEqn);
    }
}
