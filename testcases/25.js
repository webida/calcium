var [e0, e1] = [1, ''];
// e0 : number, e1 : string
var {f1, f2: v2} = {f1: 1, f2: ''};
// f1 : number, v2 : string
var {a : x1 = 1} = {};
// x1 : number;
var {a : x2 = 1} = {a : ''};
// x2 : number|string
