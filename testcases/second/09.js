var obj = {a: {a: '', b: 0}, b: false, c: ''};
var x = obj.a.;

var arr = [1,2,[3,{a: 1, b: false}]];
var x1 = arr[2][""];
var x2 = arr[2][1][""];
