var [e0, e1] = [1, ''];
// e0 : number, e1 : string
var {f1, f2: v2} = {f1: 1, f2: ''};
// f1 : number, v2 : string
var {a : x1 = 1} = {};
// x1 : number;
var {a : x2 = 1} = {a : ''};
// x2 : number|string

var x3, x4;
function fn1({a, b}) {
    x3 = a;
    x4 = b;
}
fn1({a:1, b: ''});

var x5, x6, x7;
function fn2({a = 1, b : b, c}) {
    var c = true;
    x5 = a;
    x6 = b;
    x7 = c;
}
fn2({a: true, b: '', c: 1});

var x8, x9;
try {
    throw ['', {a: 1}];
} catch ([e0, {a}]) {
    x8 = e0;
    x9 = a;
}

var x10, x11;
function fn3(a, ...rest) {
    x10 = rest[0];
    x11 = rest[1];
}
fn3(1, '', true);
